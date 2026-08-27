import CausalDagCgka.Authorization
import CausalDagCgka.Puncture

namespace CausalDagCgka

/--
The convergent public protocol state. It contains normalized membership and
per-member capabilities, valid fork facts, accepted retrospective grants, and
public punctures. No secret key material occurs here.
-/
structure PublicState
    (Member Capability MemberTag CapabilityTag Fork Grant Index : Type) where
  authorization : AuthorizationState Member Capability MemberTag CapabilityTag
  validForks : Fork → Prop
  grants : Grant → Prop
  punctures : PunctureSet Index

namespace PublicState

variable
  {Member Capability MemberTag CapabilityTag Fork Grant Index : Type}

/-- Empty public state. -/
def empty :
    PublicState Member Capability MemberTag CapabilityTag Fork Grant Index where
  authorization := AuthorizationState.empty
  validForks := fun _ => False
  grants := fun _ => False
  punctures := fun _ => False

/-- Componentwise state-based CRDT join. -/
def join
    (a b :
      PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) :
    PublicState Member Capability MemberTag CapabilityTag Fork Grant Index where
  authorization := AuthorizationState.join a.authorization b.authorization
  validForks := predUnion a.validForks b.validForks
  grants := predUnion a.grants b.grants
  punctures := PunctureSet.join a.punctures b.punctures

/-- Extensional equality. -/
theorem ext
    {a b :
      PublicState Member Capability MemberTag CapabilityTag Fork Grant Index}
    (hAuthorization : a.authorization = b.authorization)
    (hValidForks : a.validForks = b.validForks)
    (hGrants : a.grants = b.grants)
    (hPunctures : a.punctures = b.punctures) : a = b := by
  cases a with
  | mk aa af ag ap =>
      cases b with
      | mk ba bf bg bp =>
          cases hAuthorization
          cases hValidForks
          cases hGrants
          cases hPunctures
          rfl

theorem join_comm
    (a b :
      PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) :
    join a b = join b a := by
  apply ext
  · exact AuthorizationState.join_comm a.authorization b.authorization
  · exact predUnion_comm a.validForks b.validForks
  · exact predUnion_comm a.grants b.grants
  · exact PunctureSet.join_comm a.punctures b.punctures

theorem join_assoc
    (a b c :
      PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) :
    join (join a b) c = join a (join b c) := by
  apply ext
  · exact AuthorizationState.join_assoc
      a.authorization b.authorization c.authorization
  · exact predUnion_assoc a.validForks b.validForks c.validForks
  · exact predUnion_assoc a.grants b.grants c.grants
  · exact PunctureSet.join_assoc a.punctures b.punctures c.punctures

theorem join_idem
    (a : PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) :
    join a a = a := by
  apply ext
  · exact AuthorizationState.join_idem a.authorization
  · exact predUnion_idem a.validForks
  · exact predUnion_idem a.grants
  · exact PunctureSet.join_idem a.punctures

/-- Apply one public delta already validated in its signed causal context. -/
def applyDelta
    (s d :
      PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) :
    PublicState Member Capability MemberTag CapabilityTag Fork Grant Index :=
  join s d

/-- Apply validated public deltas in any replay order. -/
def applyAll :
    PublicState Member Capability MemberTag CapabilityTag Fork Grant Index →
    List
      (PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) →
    PublicState Member Capability MemberTag CapabilityTag Fork Grant Index
  | s, [] => s
  | s, d :: ds => applyAll (applyDelta s d) ds

/-- Adjacent public deltas commute. -/
theorem applyAll_swap
    (s a b :
      PublicState Member Capability MemberTag CapabilityTag Fork Grant Index)
    (rest :
      List
        (PublicState Member Capability MemberTag CapabilityTag Fork Grant Index)) :
    applyAll s (a :: b :: rest) = applyAll s (b :: a :: rest) := by
  have h : join (join s a) b = join (join s b) a := by
    rw [join_assoc, join_assoc]
    rw [join_comm a b]
  exact congrArg (fun state => applyAll state rest) h

/--
Full public-state confluence: every permutation of the same validated deltas
produces the same `(Members, Capabilities, ValidForks, Grants, Punctures)` state.
-/
theorem applyAll_perm
    {xs ys :
      List
        (PublicState Member Capability MemberTag CapabilityTag Fork Grant Index)}
    (h : xs.Perm ys)
    (s : PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) :
    applyAll s xs = applyAll s ys := by
  induction h generalizing s with
  | nil => rfl
  | cons x h ih =>
      exact ih (applyDelta s x)
  | swap x y rest =>
      exact applyAll_swap s y x rest
  | trans h₁ h₂ ih₁ ih₂ =>
      exact (ih₁ s).trans (ih₂ s)

/-- The public convergence spine is a join-semilattice. -/
theorem strong_eventual_consistency_pair
    (leftState rightState :
      PublicState Member Capability MemberTag CapabilityTag Fork Grant Index) :
    join leftState rightState = join rightState leftState :=
  join_comm leftState rightState

end PublicState

end CausalDagCgka
