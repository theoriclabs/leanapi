import LeanDb.Model
import LeanApi.Core
import LeanApi.Native
open LeanDb.Model LeanApi.Core

-- An app with no accounts cannot serve an operation that needs a signed-in user.
namespace Board

structure Member where
  name : Name
  deriving Entity

structure Note where
  author : Ref Member
  text   : Text
  deriving Entity

structure SignedIn where
  private mk ::
  id : Ref Member
  deriving Principal

def write (me : SignedIn) (text : Text) : Op Empty (Ref Note) :=
  Note.insert { author := me.id, text }

def api : Api := [
  post "/notes" write
]

end Board

app% board where
  api := Board.api
