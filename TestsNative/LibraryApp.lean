import LeanDb.Model
import LeanApi.Core
import LeanApi.Native

/-! Generality fixture: a library-loans app, unrelated to the Partiful fixtures, built only
from public API (portable `deriving Entity`, `constraint`, `internal`, `deriving Changes`,
`deriving Principal`, `link`, `credential`, a cascade constraint, plain operations,
`def api : Api`; LeanAPI's `app%` with the declared credential, and a migration). It exercises the same features as the post's app:
a composite unique as a typed conflict, a cascade on book delete, a loan-history join, a
librarian-only rule, a `ReadOp` on GET with an `Option SignedIn` reader, `SignedIn` commands,
and authored sign-up/sign-in whose KDF work is prepared before writer admission.

`V1` is the library before books had a shelf; the current domain adds `Book.shelf` with a
migration. `scripts/ddd_library_acceptance.mjs` runs both over real curl and SQLite. -/

namespace Library
open LeanDb.Model LeanApi.Core

inductive Shelf where
  | general | reference
  deriving Domain

deriving instance BEq for Shelf

inductive JoinError where
  | emailTaken

inductive SignInError where
  | wrongEmailOrPassword

inductive BookError where
  | notFound

inductive ShelveError where
  | notFound
  | librarianOnly

inductive BorrowError where
  | notFound
  | alreadyBorrowed

inductive ProfileError where
  | notFound

/-! ## The library before shelves (first deployment) -/

namespace V1
structure Member where
  name      : Name
  email     : Email
  librarian : Bool
  deriving Entity

structure Book where
  title : Title
  deriving Entity

structure Loan where
  book   : Ref Book
  member : Ref Member
  deriving Entity

structure MemberCredential where
  member : Ref Member
  hash   : PasswordHash
  deriving Entity

constraint Member.uniqueEmail : unique email
constraint Loan.onePerMember : unique (book, member)
constraint Loan.removeWithBook : cascade book
credential MemberCredential.member MemberCredential.hash

structure SignedIn where
  private mk ::
  id : Ref Member
  deriving Principal

def join (name : Name) (email : Email) (password : Password) : Op JoinError Session := do
  match ← Member.insert { name, email, librarian := false } with
  | .error .uniqueEmail => throw .emailTaken
  | .ok id =>
    let _ ← MemberCredential.insert { member := id, hash := ← password.hash }
    Auth.startSession id

def addBook (me : V1.SignedIn) (title : Title) : Op ShelveError (Ref Book) := do
  let some member ← Member.find me.id | throw .notFound
  let ⟨_⟩ ← require (member.librarian = true) .librarianOnly
  Book.insert { title }

def api : Api := [
  post "/join"  join,
  post "/books" addBook
]
end V1

/-! ## The current library -/

structure Member where
  name      : Name
  email     : Email
  librarian : Bool
  deriving Entity

structure Book where
  title : Title
  shelf : Shelf
  deriving Entity

structure Loan where
  book   : Ref Book
  member : Ref Member
  deriving Entity

structure MemberCredential where
  member : Ref Member
  hash   : PasswordHash
  deriving Entity

constraint Member.uniqueEmail : unique email
constraint Loan.onePerMember : unique (book, member)
-- Removing a book removes its loans; a member with loans cannot be removed.
constraint Loan.removeWithBook : cascade book
-- The loan history joins loans to the members who took them.
link Loan.book Loan.member
credential MemberCredential.member MemberCredential.hash
-- Loan rows are read only through the loan-history join; a profile edit changes the name only.
internal Loan.select
deriving instance Changes (except := [email, librarian]) for Member

structure SignedIn where
  private mk ::
  id : Ref Member
  deriving Principal

def join (name : Name) (email : Email) (password : Password) : Op JoinError Session := do
  match ← Member.insert { name, email, librarian := false } with
  | .error .uniqueEmail => throw .emailTaken
  | .ok id =>
    let _ ← MemberCredential.insert { member := id, hash := ← password.hash }
    Auth.startSession id

def signIn (email : Email) (password : Password) : Op SignInError Session := do
  let some id ← MemberCredential.verify (← Member.findBy email) password
    | throw .wrongEmailOrPassword
  Auth.startSession id

/-- Librarians shelve books. -/
def addBook (me : SignedIn) (title : Title) (shelf : Shelf) : Op ShelveError (Ref Book) := do
  let some member ← Member.find me.id | throw .notFound
  let ⟨_⟩ ← require (member.librarian = true) .librarianOnly
  Book.insert { title, shelf }

/-- Removing a book removes its loans (`Loan.removeWithBook`). -/
def removeBook (me : SignedIn) (book : Ref Book) : Op ShelveError Unit := do
  let some member ← Member.find me.id | throw .notFound
  let ⟨_⟩ ← require (member.librarian = true) .librarianOnly
  let some b ← Book.find book | throw .notFound
  Book.delete b

/-- One loan per member and book: the second is the `onePerMember` conflict, a typed error. -/
def borrow (me : SignedIn) (book : Ref Book) : Op BorrowError (Ref Loan) := do
  let some _ ← Book.find book | throw .notFound
  match ← Loan.insert { book, member := me.id } with
  | .ok id => pure id
  | .error .onePerMember => throw .alreadyBorrowed

structure Borrower where
  name : Name

structure BookPage where
  title     : Title
  shelf     : Shelf
  borrowers : List Borrower

/-- Anyone may read a book's page; the borrowers come from one join (Loan ⋈ Member). -/
def bookPage (reader : Option SignedIn) (book : Ref Book) : ReadOp BookError BookPage := do
  let some b ← Book.find book | throw .notFound
  let names ← Query.linkField Loan.link.book.member Member.namePath book
  return { title := b.title, shelf := b.shelf, borrowers := names.map Borrower.mk }

def editProfile (me : SignedIn) (changes : Member.Changes) : Op ProfileError Unit := do
  let some m ← Member.find me.id | throw .notFound
  Member.patch m changes

def api : Api := [
  post "/join"                join,
  post "/sign-in"             signIn,
  post "/books"               addBook,
  get  "/books/:book"         bookPage,
  post "/books/:book/loans"   borrow,
  post "/books/:book/remove"  removeBook,
  post "/me"                  editProfile
]
end Library

app% LibraryV1 where
  authentication := Library.V1.Member with Library.V1.MemberCredential
  api := Library.V1.api

app% LibraryApp where
  authentication := Library.Member with Library.MemberCredential
  api := Library.api
  migrations := [
    addShelf := Library.Book.addField shelf (fill := .general)
  ]

/-- `library (v1 | v2 | v2-unmigrated) [migrate [--check]]`. -/
def Library.main (args : List String) : IO UInt32 := do
  let config : LeanApi.Native.AppConfig := { database := "library.sqlite" }
  match args with
  | "v1" :: rest => LibraryV1.main rest config
  | "v2" :: rest => LibraryApp.main rest config
  | "v2-unmigrated" :: rest => LeanApi.Native.NativeApp.main { LibraryApp with migrations := [] } rest config
  | _ => do
    IO.eprintln "usage: leanapi_apps library (v1 | v2 | v2-unmigrated) [migrate [--check]]"
    return 2
