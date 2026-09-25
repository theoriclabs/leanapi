import LeanApi
open LeanApi

def hello : Text := ⟨"Hello World!"⟩

def app : Api Unit := api! [.get "/" hello]

def main : IO Unit := app.listen 3000
