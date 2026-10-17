/-
# Validation probes — reading the API element form

A hand-built element list in the shape OpenSysML's `-convert api-json` writes, covering each
convention the reader relies on: the keyword from the metadata definition's short name, a
redefinition chain through an inherited default (`width :> length`), a nested record as a
subsetting usage, a sequence value, a negative literal (`OperatorExpression -`), a reference
value (an enumeration literal, a kind), connection ends by `ReferenceSubsetting`, citations,
and scale inheritance through specialization.
-/

module

public import PropertyKindCalculus.Interchange
meta import PropertyKindCalculus.Interchange

@[expose] public section Blanket

namespace PropertyKindCalculus.Tests.Interchange.ApiJson

open Lean PropertyKindCalculus.Interchange

/-- An element object. -/
def el (id type : String) (props : List (String × Json) := []) : Json :=
  Json.mkObj ([("@id", Json.str id), ("@type", Json.str type)] ++ props)

def ref (id : String) : Json := Json.mkObj [("@id", id)]

def lib (id type name : String) (props : List (String × Json) := []) : Json :=
  el id type ([("declaredName", Json.str name), ("qualifiedName", Json.str s!"PKC::{name}")] ++ props)

/-- `:>> field = value` on `owner`, redefining `target`. -/
def binding (owner target field : String) (value : Json) (dflt := false) : List Json :=
  let f := s!"{owner}__{field}"
  [el f "ReferenceUsage" [("owner", ref owner), ("value", ref s!"{f}_v"), ("isDefault", Json.bool dflt),
     ("ownedRelationship", Json.arr #[ref s!"{f}_rd"])],
   el s!"{f}_rd" "Redefinition" [("owner", ref f), ("redefinedFeature", ref target)],
   value]

def litStr (id s : String) : Json := el id "LiteralString" [("value", Json.str s)]
def litInt (id : String) (n : Int) : Json := el id "LiteralInteger" [("value", toJson n)]
def fre (id target : String) : Json := el id "FeatureReferenceExpression" [("referent", ref target)]

/-- The DSL library fragment the fixture needs. -/
def library : List Json :=
  [lib "PKC" "Package" "PKC" [("qualifiedName", Json.str "PKC")],
   lib "K_Kind" "MetadataDefinition" "Kind" [("declaredShortName", Json.str "kind")],
   lib "K_Product" "MetadataDefinition" "Product" [("declaredShortName", Json.str "product")],
   lib "K_Tape" "MetadataDefinition" "TapeOf" [("declaredShortName", Json.str "tape")],
   lib "K_Checked" "MetadataDefinition" "Checked", lib "K_Checked_decl" "AttributeUsage" "decl",
   lib "KOP_id" "AttributeUsage" "id", lib "KOP_scale" "AttributeUsage" "scale",
   lib "KOP_dimension" "AttributeUsage" "dimension",
   lib "DE_base" "AttributeUsage" "base", lib "DE_num" "AttributeUsage" "num",
   lib "TG_vertices" "AttributeUsage" "vertices", lib "TV_name" "AttributeUsage" "name",
   lib "TV_parents" "AttributeUsage" "parents",
   lib "ST_ratio" "EnumerationUsage" "ratio" [("qualifiedName", Json.str "PKC::Kinds::ScaleType::ratio")]]

/-- `#kind length { :>> id default = "length"; :>> scale default = ratio;
attribute dimL :> dimension { :>> base = "length"; :>> num = -1; } }`,
`#kind width :> length { :>> id default = "width"; @Checked { decl = "E.w" } }`,
`#product connection p : KindProduct connect (left ::> length, right ::> width, result ::> width)`,
`#tape t : TapeGraph { attribute v0 :> vertices { :>> name = "k"; :>> parents = (0, 1); } }`. -/
def model : List Json :=
  [el "M" "Package" [("declaredName", Json.str "M"), ("qualifiedName", Json.str "M")],
   -- length
   el "M__length" "ReferenceUsage" [("declaredName", Json.str "length"), ("owner", ref "M"),
     ("ownedRelationship", Json.arr #[ref "M__length_mu"])],
   el "M__length_mu" "MetadataUsage" [("owner", ref "M__length"), ("type", Json.arr #[ref "K_Kind"])]]
  ++ binding "M__length" "KOP_id" "id" (litStr "M__length__id_v" "length") true
  ++ binding "M__length" "KOP_scale" "scale" (fre "M__length__scale_v" "ST_ratio") true
  ++ [el "M__length__dimL" "AttributeUsage" [("declaredName", Json.str "dimL"), ("owner", ref "M__length"),
        ("ownedRelationship", Json.arr #[ref "M__length__dimL_ss"])],
      el "M__length__dimL_ss" "Subsetting" [("owner", ref "M__length__dimL"), ("subsettedFeature", ref "KOP_dimension")]]
  ++ binding "M__length__dimL" "DE_base" "base" (litStr "M__length__dimL__base_v" "length")
  ++ binding "M__length__dimL" "DE_num" "num"
       (el "M__length__dimL__num_v" "OperatorExpression" [("operator", Json.str "-"),
          ("ownedRelationship", Json.arr #[ref "M__length__dimL__num_v_pin_om"])])
  ++ [el "M__length__dimL__num_v_pin_om" "ParameterMembership" [("owner", ref "M__length__dimL__num_v"),
        ("ownedRelatedElement", Json.arr #[ref "M__length__dimL__num_v_pin"])],
      el "M__length__dimL__num_v_pin" "Feature" [("owner", ref "M__length__dimL__num_v"),
        ("ownedRelationship", Json.arr #[ref "M__length__dimL__num_v_pin_fv"])],
      el "M__length__dimL__num_v_pin_fv" "FeatureValue" [("owner", ref "M__length__dimL__num_v_pin"),
        ("value", ref "M__length__dimL__num_v_lit")],
      litInt "M__length__dimL__num_v_lit" 1,
   -- width :> length
   el "M__width" "ReferenceUsage" [("declaredName", Json.str "width"), ("owner", ref "M"),
     ("ownedRelationship", Json.arr #[ref "M__width_mu", ref "M__width_ss"])],
   el "M__width_mu" "MetadataUsage" [("owner", ref "M__width"), ("type", Json.arr #[ref "K_Kind"])],
   el "M__width_ss" "Subsetting" [("owner", ref "M__width"), ("subsettedFeature", ref "M__length")],
   el "M__width_chk" "MetadataUsage" [("owner", ref "M__width"), ("type", Json.arr #[ref "K_Checked"])]]
  ++ binding "M__width_chk" "K_Checked_decl" "decl" (litStr "M__width_chk__decl_v" "E.w")
  -- the chain: width.id redefines length.id, which redefines the library's id
  ++ binding "M__width" "M__length__id" "id" (litStr "M__width__id_v" "width") true
  ++ [-- product connection
      el "M__p" "ConnectionUsage" [("declaredName", Json.str "p"), ("owner", ref "M"),
        ("connectorEnd", Json.arr #[ref "M__p_e0", ref "M__p_e1", ref "M__p_e2"])],
      el "M__p_mu" "MetadataUsage" [("owner", ref "M__p"), ("type", Json.arr #[ref "K_Product"])],
      el "M__p_e0" "ReferenceUsage" [("owner", ref "M__p"), ("ownedRelationship", Json.arr #[ref "M__p_e0_rs"])],
      el "M__p_e0_rs" "ReferenceSubsetting" [("owner", ref "M__p_e0"), ("referencedFeature", ref "M__length")],
      el "M__p_e1" "ReferenceUsage" [("owner", ref "M__p"), ("ownedRelationship", Json.arr #[ref "M__p_e1_rs"])],
      el "M__p_e1_rs" "ReferenceSubsetting" [("owner", ref "M__p_e1"), ("referencedFeature", ref "M__width")],
      el "M__p_e2" "ReferenceUsage" [("owner", ref "M__p"), ("ownedRelationship", Json.arr #[ref "M__p_e2_rs"])],
      el "M__p_e2_rs" "ReferenceSubsetting" [("owner", ref "M__p_e2"), ("referencedFeature", ref "M__width")],
      -- tape
      el "M__t" "AttributeUsage" [("declaredName", Json.str "t"), ("owner", ref "M")],
      el "M__t_mu" "MetadataUsage" [("owner", ref "M__t"), ("type", Json.arr #[ref "K_Tape"])],
      el "M__t__v0" "AttributeUsage" [("declaredName", Json.str "v0"), ("owner", ref "M__t"),
        ("ownedRelationship", Json.arr #[ref "M__t__v0_ss"])],
      el "M__t__v0_ss" "Subsetting" [("owner", ref "M__t__v0"), ("subsettedFeature", ref "TG_vertices")]]
  ++ binding "M__t__v0" "TV_name" "name" (litStr "M__t__v0__name_v" "k")
  ++ binding "M__t__v0" "TV_parents" "parents"
       (el "M__t__v0__parents_v" "OperatorExpression" [("operator", Json.str ","),
          ("ownedRelationship", Json.arr #[ref "M__t__v0__parents_v_p0_om", ref "M__t__v0__parents_v_p1_om"])])
  ++ [el "M__t__v0__parents_v_p0_om" "ParameterMembership" [("owner", ref "M__t__v0__parents_v")],
      el "M__t__v0__parents_v_p0" "Feature" [("owner", ref "M__t__v0__parents_v"), ("value", ref "M__t__v0__parents_v_l0")],
      litInt "M__t__v0__parents_v_l0" 0,
      el "M__t__v0__parents_v_p1" "Feature" [("owner", ref "M__t__v0__parents_v"), ("value", ref "M__t__v0__parents_v_l1")],
      litInt "M__t__v0__parents_v_l1" 1]

def fixture : String := (Json.arr (library ++ model).toArray).compress

/-- The reader recovers the model. -/
def readModel : Except String (PkcModel × Array String) :=
  PropertyKindCalculus.Interchange.ApiJson.read fixture

def got : PkcModel := match readModel with | .ok (m, _) => m | .error _ => default
def warningCount : Nat := match readModel with | .ok (_, w) => w.size | .error _ => 1000
def readError : String := match readModel with | .ok _ => "" | .error e => e

#guard readError == ""
#guard got.packageName == "M"
#guard warningCount == 0
#guard got.kinds.map (·.name) == ["length", "width"]
#guard (got.kind? "length").map (·.id) == some "length"
#guard (got.kind? "length").map (·.dimension) == some [{ base := "length", num := -1, den := 1 }]
#guard (got.kind? "width").map (·.id) == some "width"
#guard (got.kind? "width").map (·.specializes) == some ["length"]
-- the species inherits the genus's scale and dimension through the subsetting
#guard (got.kind? "width").map (·.scale) == some .ratio
#guard (got.kind? "width").map (·.dimension) == some [{ base := "length", num := -1, den := 1 }]
#guard (got.kind? "width").map (·.checked) == some [{ decl := "E.w" }]
#guard got.edges.map (·.kind) == [.product]
#guard got.edges.map (·.operands) == [["length", "width"]]
#guard got.edges.map (·.result) == [some "width"]
#guard got.tapes.map (·.vertices) == [[{ name := some "k", parents := [0, 1] }]]
-- what is read reads back from its JSON unchanged, and emits as a package in the DSL
#guard (match PkcModel.ofJsonString got.toJsonString with | .ok m => m == got | .error _ => false)
#guard (EmitSysml.emit got).startsWith "package M {"

end PropertyKindCalculus.Tests.Interchange.ApiJson

end Blanket
