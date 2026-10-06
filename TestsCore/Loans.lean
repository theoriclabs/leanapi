/- Generality fixture (the user's "libraries stay general" requirement): a lending library,
   unrelated to the post, built only from the public API. It exercises what the post uses:
   a composite unique constraint, a cascade, a link join, `internal` raw operations, a
   `Changes` record, a rule that takes a proof, a `ReadOp`, typed errors, credential auth,
   and typed endpoints (its pages are LeanReact's). `LoansRun.lean` runs it in memory. -/
import LeanDb.Model
import LeanApi.Core
open LeanDb.Model LeanApi.Core

namespace Loans

/-! ## Entities and declarations -/

inductive MemberRole where
  | reader
  | librarian
  deriving DecidableEq

structure Member where
  name  : Name
  email : Email
  role  : MemberRole
  deriving Entity

structure Book where
  title   : Title
  notes   : Text
  addedBy : Ref Member
  deriving Entity

structure Loan where
  book   : Ref Book
  member : Ref Member
  deriving Entity

structure Login where
  member : Ref Member
  secret : PasswordHash
  deriving Entity

-- Explicit opt-in: `Login` is the credential table (generates `Login.verify`).
credential Login.member Login.secret
-- The loan history joins loans to the members who borrowed.
link Loan.book Loan.member
-- Raw loan reads/writes and book deletion stay in this module.
internal Loan.select, Loan.insert, Book.delete
-- An edit cannot change who added the book.
deriving instance Changes (except := [addedBy]) for Book

constraint Member.uniqueEmail : unique email
constraint Loan.oneActive : unique (book, member)
-- Removing a book removes its loans.
constraint Loan.removeWithBook : cascade book

/-- info: Loans.Loan.insert : Loan → DB (Except Loan.Conflict (Ref Loan)) -/
#guard_msgs in #check Loan.insert
/-- info: Loans.Loan.findBy : Ref Book → Ref Member → Query (Option (Row Loan)) -/
#guard_msgs in #check Loan.findBy
/-- info: Loans.Book.patch : Row Book → Book.Changes → DB Unit -/
#guard_msgs in #check Book.patch
/-- info: Loans.Login.verify {ε : Type} : Option (Row Member) → Password → Op ε (Option (Ref Member)) -/
#guard_msgs in #check Login.verify
/-- info: Loans.Loan.link.book.member : LinkKey Loan Book Member -/
#guard_msgs in #check Loan.link.book.member
#guard (HasRecord.fieldMetadata (T := Book.Changes)).map (·.name) == ["title", "notes"]

structure Patron where
  private mk ::
  id : Ref Member
  deriving Principal

/-! ## Rules -/

/-- Only librarians add, edit and retire books, and see a book's loan history. -/
abbrev IsLibrarian (m : Row Member) : Prop :=
  m.role = .librarian

structure Borrower where
  name : Name

inductive LoanHistory where
  | visible (borrowers : List Borrower)
  | hidden

/-- Who borrowed this book, by member id: one typed join (Loan ⋈ Member) selecting `name`.
Takes the proof that the viewer is a librarian. -/
def Book.history (b : Row Book) (viewer : Row Member) (_h : IsLibrarian viewer) : Query (List Borrower) :=
  (·.map Borrower.mk) <$> Query.linkField Loan.link.book.member Member.namePath b.id

/-- The only way to delete a book; its loans go with it (`Loan.removeWithBook`). -/
def Book.retire (b : Row Book) (librarian : Row Member) (_h : IsLibrarian librarian) : DB Unit :=
  Book.delete b

/-- Borrow as yourself. -/
def Loan.open (b : Row Book) (me : Patron) : DB (Except Loan.Conflict Unit) := do
  match ← Loan.insert { book := b.id, member := me.id } with
  | .ok _ => return .ok ()
  | .error conflict => return .error conflict

/-! ## Operations -/

inductive RegisterError where
  | alreadyRegistered

def register (name : Name) (email : Email) (password : Password) : Op RegisterError Session := do
  match ← Member.insert { name, email, role := .reader } with
  | .error .uniqueEmail => throw .alreadyRegistered
  | .ok id =>
    let _ ← Login.insert { member := id, secret := ← password.hash }
    Auth.startSession id

inductive LogInError where
  | badCredentials

def logIn (email : Email) (password : Password) : Op LogInError Session := do
  let some id ← Login.verify (← Member.findBy email) password
    | throw .badCredentials
  Auth.startSession id

inductive AddBookError where
  | notLibrarian

def addBook (me : Patron) (title : Title) (notes : Text) : Op AddBookError (Ref Book) := do
  let some member ← Member.find me.id | throw .notLibrarian
  let ⟨_isLibrarian⟩ ← require (IsLibrarian member) .notLibrarian
  Book.insert { title, notes, addedBy := me.id }

inductive BorrowError where
  | notFound
  | alreadyBorrowed

def borrow (me : Patron) (book : Ref Book) : Op BorrowError Unit := do
  let some b ← Book.find book | throw .notFound
  match ← Loan.open b me with
  | .ok _ => pure ()
  | .error .oneActive => throw .alreadyBorrowed

structure BookPage where
  title   : Title
  notes   : Text
  history : LoanHistory

inductive GetBookError where
  | notFound

def getBook (viewer : Option Patron) (book : Ref Book) : ReadOp GetBookError BookPage := do
  let some b ← Book.find book | throw .notFound
  let member ← match viewer with
    | some me => Member.find me.id
    | none => pure none
  let history ← match member with
    | some m =>
      if h : IsLibrarian m then LoanHistory.visible <$> Book.history b m h else pure .hidden
    | none => pure .hidden
  return { title := b.title, notes := b.notes, history }

inductive RetireError where
  | notFound
  | notLibrarian

def retire (me : Patron) (book : Ref Book) : Op RetireError Unit := do
  let some b ← Book.find book | throw .notFound
  let some member ← Member.find me.id | throw .notLibrarian
  let ⟨isLibrarian⟩ ← require (IsLibrarian member) .notLibrarian
  Book.retire b member isLibrarian

inductive EditBookError where
  | notFound
  | notLibrarian

def editBook (me : Patron) (book : Ref Book) (changes : Book.Changes) : Op EditBookError Unit := do
  let some b ← Book.find book | throw .notFound
  let some member ← Member.find me.id | throw .notLibrarian
  let ⟨_isLibrarian⟩ ← require (IsLibrarian member) .notLibrarian
  Book.patch b changes

/-! ## Endpoints -/

def api : Api := [
  post "/members"            register,
  post "/log-in"             logIn,
  post "/books"              addBook,
  get  "/books/:book"        getBook,
  post "/books/:book/loans"  borrow,
  post "/books/:book/retire" retire
]

derive_operation editBook

/-- info: Loans.api.borrow (book : Ref Book) : Endpoint borrow.Input BorrowError Unit -/
#guard_msgs in #check api.borrow
#guard (api.map fun e => (e.method.name, e.path)) ==
  [("POST", "/members"), ("POST", "/log-in"), ("POST", "/books"), ("GET", "/books/:book"),
   ("POST", "/books/:book/loans"), ("POST", "/books/:book/retire")]
#guard register.operation.metadata.kdf == [.hash "password"] && logIn.operation.metadata.kdf == [.verify "password"]
#guard register.operation.metadata.establishesSession
#guard getBook.operation.contract.kind == .query
#guard (getBook.operation.metadata.nodes.map (·.kind)).contains "linkField"
#guard !(getBook.operation.metadata.nodes.map (·.kind)).contains "select"
#guard retire.operation.metadata.failures == ["notFound", "notLibrarian"]

end Loans
