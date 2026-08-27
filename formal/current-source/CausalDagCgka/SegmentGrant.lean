import CausalDagCgka.RegionCover

namespace CausalDagCgka

/-- A content-key coordinate in a segment-local linear namespace. -/
structure SegmentedIndex (Segment : Type) (depth : Nat) where
  segment : Segment
  position : Bits depth

/-- One retrospective authorization component: a prefix of one segment. -/
structure SegmentPrefix (Segment : Type) (depth : Nat) where
  segment : Segment
  shape : PrefixRegion depth

/-- One constrained subtree capability tagged with the segment it belongs to. -/
structure SegmentBlock (Segment : Type) (depth : Nat) where
  segment : Segment
  block : Block depth

namespace SegmentGrant

variable {Segment : Type} {depth : Nat}

/-- Semantic membership in a single segment-prefix grant. -/
def prefixContains (grant : SegmentPrefix Segment depth)
    (index : SegmentedIndex Segment depth) : Prop :=
  grant.segment = index.segment ∧
    PrefixRegion.contains grant.shape index.position

/-- Semantic membership in a tagged subtree capability. -/
def blockContains (cap : SegmentBlock Segment depth)
    (index : SegmentedIndex Segment depth) : Prop :=
  cap.segment = index.segment ∧ Block.contains cap.block index.position

/-- Canonical constrained-key cover for one segment prefix. -/
def coverPrefix (grant : SegmentPrefix Segment depth) :
    List (SegmentBlock Segment depth) :=
  (PrefixRegion.cover grant.shape).map
    (fun block => ⟨grant.segment, block⟩)

/-- One tagged prefix is covered exactly: no under-grant and no over-grant. -/
theorem coverPrefix_exact (grant : SegmentPrefix Segment depth)
    (index : SegmentedIndex Segment depth) :
    prefixContains grant index ↔
      ∃ cap ∈ coverPrefix grant, blockContains cap index := by
  constructor
  · intro h
    rcases h with ⟨hseg, hprefix⟩
    have hcover := (PrefixRegion.cover_exact grant.shape index.position).mp hprefix
    rcases hcover with ⟨block, hmem, hcontains⟩
    refine ⟨⟨grant.segment, block⟩, ?_, ?_⟩
    · exact List.mem_map.mpr ⟨block, hmem, rfl⟩
    · exact ⟨hseg, hcontains⟩
  · intro h
    rcases h with ⟨cap, hmem, hcontains⟩
    rcases List.mem_map.mp hmem with ⟨block, hblock, hcap⟩
    subst cap
    rcases hcontains with ⟨hseg, htree⟩
    exact ⟨hseg, (PrefixRegion.cover_exact grant.shape index.position).mpr
      ⟨block, hblock, htree⟩⟩

/-- A single segment prefix needs at most `depth + 1` subtree capabilities. -/
theorem coverPrefix_length_le (grant : SegmentPrefix Segment depth) :
    (coverPrefix grant).length ≤ depth + 1 := by
  simpa [coverPrefix] using
    PrefixRegion.cover_length_le_depth_plus_one grant.shape

/-- Semantic membership in a bounded union of segment prefixes. -/
def contains (grants : List (SegmentPrefix Segment depth))
    (index : SegmentedIndex Segment depth) : Prop :=
  ∃ grant ∈ grants, prefixContains grant index

/-- Flatten all canonical covers. -/
def cover (grants : List (SegmentPrefix Segment depth)) :
    List (SegmentBlock Segment depth) :=
  grants.flatMap coverPrefix

/-- The bounded-union cover is extensionally exact. -/
theorem cover_exact (grants : List (SegmentPrefix Segment depth))
    (index : SegmentedIndex Segment depth) :
    contains grants index ↔
      ∃ cap ∈ cover grants, blockContains cap index := by
  induction grants with
  | nil =>
      simp [contains, cover]
  | cons grant rest ih =>
      constructor
      · intro h
        rcases h with ⟨selected, hselected, hcontains⟩
        simp only [List.mem_cons] at hselected
        cases hselected with
        | inl hhead =>
            subst selected
            have hcovered := (coverPrefix_exact grant index).mp hcontains
            rcases hcovered with ⟨cap, hcap, hsem⟩
            refine ⟨cap, ?_, hsem⟩
            simp only [cover, List.flatMap_cons, List.mem_append]
            exact Or.inl hcap
        | inr htail =>
            have hcovered := ih.mp ⟨selected, htail, hcontains⟩
            rcases hcovered with ⟨cap, hcap, hsem⟩
            refine ⟨cap, ?_, hsem⟩
            simp only [cover, List.flatMap_cons, List.mem_append]
            exact Or.inr hcap
      · intro h
        rcases h with ⟨cap, hcap, hsem⟩
        simp only [cover, List.mem_flatMap] at hcap
        rcases hcap with ⟨selected, hselected, hcapSelected⟩
        have hprefix := (coverPrefix_exact selected index).mpr
          ⟨cap, hcapSelected, hsem⟩
        exact ⟨selected, by simp [hselected], hprefix⟩

/--
A grant touching `b = grants.length` segments needs at most
`b * (depth + 1)` constrained subtree seeds.
-/
theorem cover_length_le (grants : List (SegmentPrefix Segment depth)) :
    (cover grants).length ≤ grants.length * (depth + 1) := by
  induction grants with
  | nil =>
      simp [cover]
  | cons grant rest ih =>
      have hgrant := coverPrefix_length_le grant
      calc
        (cover (grant :: rest)).length
            = (coverPrefix grant).length + (cover rest).length := by
              simp [cover]
        _ ≤ (depth + 1) + rest.length * (depth + 1) :=
              Nat.add_le_add hgrant ih
        _ = rest.length * (depth + 1) + (depth + 1) := Nat.add_comm _ _
        _ = (rest.length + 1) * (depth + 1) := by
              rw [Nat.add_mul]
              simp
        _ = (grant :: rest).length * (depth + 1) := by
              simp

end SegmentGrant

end CausalDagCgka
