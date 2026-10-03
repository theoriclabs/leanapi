import LeanApiDomain.AuthStorage
import LeanDbDomain.Resources
import LeanDbDomain.Access

namespace LeanApi.Domain.Native
open LeanApp.Domain

/-- DB owns the coherent entity/member/column family; API fills its dependent
private-auth slot. This uses the ONE portable resource vocabulary. -/
@[reducible] def resources (s : Type) [LeanDb.IsSchema s] : ResourceFamily :=
  { LeanDb.Domain.storageResources s with auth := fun storage => Auth.Storage s _ storage }

@[reducible] instance {s T} [LeanDb.IsSchema s] [LeanDb.Domain.HasEntityStorage s T] :
    HasEntityResource (resources s) T := ⟨LeanDb.Domain.HasEntityStorage.storage⟩
@[reducible] instance {s P T field} [LeanDb.IsSchema s] [LeanDb.Domain.HasMemberStorage s P field T] :
    HasMemberResource (resources s) P field T := ⟨LeanDb.Domain.HasMemberStorage.storage (s := s) (Parent := P) (field := field) (Target := T)⟩
instance {s P T member field V} [LeanDb.IsSchema s] [EditableField T field V]
    (storage : (resources s).member P member T)
    [selection : HasProjectionResource (LeanDb.Domain.storageResources s) P T member storage field V] :
    HasProjectionResource (resources s) P T member storage field V := ⟨selection.witness⟩
@[reducible] instance {s T} [LeanDb.IsSchema s] (storage : (resources s).entity T)
    [Auth.HasStorage s T storage] : HasAuthResource (resources s) T storage :=
  ⟨Auth.HasStorage.storage⟩
/-- Declared unique constraints (`T.findBy`, DDD-LR-05) use exactly the evidence LeanDB's
family provides; LeanAPI adds none of its own. -/
@[reducible] instance {s T K} [LeanDb.IsSchema s] (storage : (resources s).entity T)
    (key : UniqueKey T K) [evidence : HasUniqueResource (LeanDb.Domain.storageResources s) T K storage key] :
    HasUniqueResource (resources s) T K storage key := ⟨evidence.witness⟩
/-- Joins (`Query.linkField`): LeanDB's link and column evidence, forwarded. -/
@[reducible] instance {s E P T} [LeanDb.IsSchema s] (storage : (resources s).entity E)
    (key : LinkKey E P T) [evidence : HasLinkResource (LeanDb.Domain.storageResources s) E P T storage key] :
    HasLinkResource (resources s) E P T storage key := ⟨evidence.witness⟩
@[reducible] instance {s T V} [LeanDb.IsSchema s] (storage : (resources s).entity T)
    (path : Ontology.FieldPath T V) [evidence : HasColumnResource (LeanDb.Domain.storageResources s) T V storage path] :
    HasColumnResource (resources s) T V storage path := ⟨evidence.witness⟩

end LeanApi.Domain.Native
