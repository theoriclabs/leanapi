import LeanApiDomain.App
import LeanApp.Core
import LeanReact.Domain

/-! Generality fixture: a library-loans app, unrelated to the Partiful fixtures, built only
from public API (portable `deriving Entity`, `constraint`, `internal`, `deriving Changes`,
`deriving Principal`, `link`, `credential`, a cascade constraint, plain operations,
`def api : Api`, a LeanReact `App` with pages; LeanAPI's `app%` serving that `App`, its
credential read from the domain, and a migration). It exercises the same features as the post's app:
a composite unique as a typed conflict, a cascade on book delete, a loan-history join, a
librarian-only rule, a `ReadOp` on GET with an `Option SignedIn` reader, `SignedIn` commands,
and authored sign-up/sign-in whose KDF work is prepared before writer admission.

`V1` is the library before books had a shelf; the current domain adds `Book.shelf` with a
migration. `scripts/ddd_library_acceptance.mjs` runs both over real curl and SQLite. -/

namespace Library
open LeanApp.Domain hiding SignedIn

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

/-! ## The library's pages: a LeanReact `App` over the current `api` -/
namespace Library.Web
open LeanApp.Core LeanReact

def joinPage : Element :=
  form api.join
    (onSuccess := fun _ => navigate "/books/new")
    (onError := fun
      | .emailTaken => fieldError "email" "This email already has a library card.")

def addBookPage : Element :=
  form api.addBook
    (onSuccess := fun book => navigate s!"/books/{book}")
    (onError := fun
      | .notFound      => notice "Sign in again."
      | .librarianOnly => notice "Only librarians shelve books.")

def borrowButton (book : Ref Book) : Action Unit :=
  call (api.borrow book)
    (onSuccess := fun _ => pure ())
    (onError := fun
      | .notFound        => notice "No such book."
      | .alreadyBorrowed => notice "You already have this book.")

def bookView (book : Ref Book) : Element :=
  load (api.bookPage book)
    (onError := fun | .notFound => DOM.p {} #[text "No such book."])
    fun page => DOM.div {} #[
      DOM.h1 {} #[text page.title],
      DOM.button { onPress := some (borrowButton book) } #[text "Borrow"],
      DOM.ul {} (page.borrowers.map fun b => DOM.li {} #[text b.name]).toArray ]

def app : App where
  api   := api
  pages := [
    "/join"        ==> joinPage,
    "/books/new"   ==> addBookPage,
    "/books/:book" ==> bookView
  ]
end Library.Web

app% LibraryV1 where
  authentication := Library.V1.Member with Library.V1.MemberCredential
  routes := []
  pages := []
  api := Library.V1.api

-- The current library is served from its `App`: the api, the pages, and the credential
-- read from the domain's `credential` declaration.
app% LibraryApp where
  app := Library.Web.app
  migrations := [
    addShelf := Library.Book.addField shelf (fill := .general)
  ]

def main (args : List String) : IO UInt32 := do
  let config : LeanApi.Domain.AppConfig := { database := "library.sqlite" }
  match args with
  | "v1" :: rest => LibraryV1.main rest config
  | "v2" :: rest => LibraryApp.main rest config
  | "v2-unmigrated" :: rest => LeanApi.Domain.NativeApp.main { LibraryApp with migrations := [] } rest config
  | _ => do
    IO.eprintln "usage: domain_library_app (v1 | v2 | v2-unmigrated) [migrate [--check]]"
    return 2
