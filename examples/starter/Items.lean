import LeanApi
open LeanApi Lean

structure Item where
  name : String
  price : Float
  isOffer : Option Bool

instance : FromBody Item := .record (Item.mk <$> .req "name" <*> .req "price" <*> .opt "is_offer")

def readRoot : Json := json% {"Hello": "World"}

def readItem (itemId : Path Int) (q : QueryParam "q" (Option String)) : Json :=
  json% {"item_id": $(itemId.val), "q": $(q.val)}

def updateItem (itemId : Path Int) (item : Body Item) : Json :=
  json% {"item_name": $(item.val.name), "item_id": $(itemId.val)}

def app : Api Unit := api! [
  .get "/"                readRoot,
  .get "/items/{item_id}" readItem,
  .put "/items/{item_id}" updateItem ]

def main : IO Unit := app.listen 8000
