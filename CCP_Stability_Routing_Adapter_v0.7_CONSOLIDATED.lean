/-!
===============================================================================
COSMOLOGICAL-CONSTANT STABILITY ROUTING ADAPTER v0.7 — CONSOLIDATED
===============================================================================

LOAD ORDER
----------
1. Structural_Flow_Universal_Kernel_v1.0.lean
2. THIS ENTIRE FILE

This consolidated file contains the already-machine-clean v0.1 routing layer,
the machine-clean v0.2 exact-kernel binding layer, the machine-clean v0.3.1
semantic layer, the v0.4 physical-successor experiment ledger earned by the
empirical-closure pressure test, and the v0.4.1 whole-history semantic repair, and the v0.5 adversarially pressure-tested case-license layer.

The v0.5 repair preserves `historyClosure = OPEN` as the governing current
physical-access blocker for direct whole-history testing while adding only
CCP-specific support / license / routing-consistency predicates earned by the
P1–P6 pressure program. Case-level licenses are conditional checks over supplied
scientific adjudications; they are not independent empirical proofs.

This file requires fresh elaboration under the unchanged Universal Kernel.

Use this file instead of the standalone v0.2 APPEND block when v0.1 is not
already present in the Lean buffer.

No Universal Kernel modification is introduced.
===============================================================================
-/

/-!
===============================================================================
COSMOLOGICAL-CONSTANT STABILITY ROUTING ADAPTER v0.1
===============================================================================

LOAD ORDER
----------
1. Structural_Flow_Universal_Kernel_v1.0.lean
2. THIS FILE

ROLE
----
This first thin adapter encodes only the frozen routing / adjudication table
from Cosmological Constant Problem — Derivation Spine v0.7.

It does NOT encode or establish:
* the numerical value of Lambda;
* QFT loop calculations;
* Wilsonian matching;
* phase-transition dynamics;
* dark-energy seat identification;
* empirical cosmology;
* or physical truth.

Physics owns the premises.
This adapter checks only the conditional routing logic.

No Universal Kernel modification is introduced.
===============================================================================
-/

namespace StructuralFlow
namespace CosmologicalConstantStabilityRouting

/-! --------------------------------------------------------------------------
Scientific four-state vocabulary
---------------------------------------------------------------------------- -/

inductive BurdenStatus where
  | pass
  | fail
  | notLive
  | unresolved
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
Frozen claim profiles
---------------------------------------------------------------------------- -/

/--
Resolved claim profiles are exactly the six lawful combinations of:
* description protection;
* successor continuity;
* successor baseline protection;

under the dependency:
successor baseline protection -> successor continuity.

`unresolved` means the scientific source has not been pinned strongly enough
to know which profile is actually claimed.
-/
inductive ClaimProfile where
  | fitOnly
  | descriptionProtection
  | successorContinuity
  | successorProtection
  | descriptionAndContinuity
  | fullProtection
  | unresolved
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
Frozen update classes
---------------------------------------------------------------------------- -/

inductive DescriptionUpdate where
  | perturbativeRefinement
  | resolutionMatching
  deriving DecidableEq, Repr

/--
`mixed d` means both:
* the description update `d`;
* and a real physical successor

are present in the same scientific case.

Mixed is therefore a routing instruction, not a third universal structural seat.
-/
inductive UpdateClass where
  | description (d : DescriptionUpdate)
  | physicalSuccessor
  | mixed (d : DescriptionUpdate)
  | unresolved
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
Frozen burden families
---------------------------------------------------------------------------- -/

inductive Burden where
  | descriptionProtection
  | successorLineage
  | successorBaselineProtection
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
Claim-profile projections
---------------------------------------------------------------------------- -/

def claimsDescriptionProtection : ClaimProfile -> Bool
  | .descriptionProtection => true
  | .descriptionAndContinuity => true
  | .fullProtection => true
  | _ => false

def claimsSuccessorContinuity : ClaimProfile -> Bool
  | .successorContinuity => true
  | .successorProtection => true
  | .descriptionAndContinuity => true
  | .fullProtection => true
  | _ => false

def claimsSuccessorBaselineProtection : ClaimProfile -> Bool
  | .successorProtection => true
  | .fullProtection => true
  | _ => false

/-! --------------------------------------------------------------------------
Update-class projections
---------------------------------------------------------------------------- -/

def hasDescriptionUpdate : UpdateClass -> Bool
  | .description _ => true
  | .mixed _ => true
  | _ => false

def hasPhysicalSuccessor : UpdateClass -> Bool
  | .physicalSuccessor => true
  | .mixed _ => true
  | _ => false

/-! --------------------------------------------------------------------------
Routing unresolved firewall
---------------------------------------------------------------------------- -/

/--
Claim uncertainty always blocks routing.

Update uncertainty blocks any cross-update claim, but a pure fit-only claim
remains NOT LIVE because it registers no cross-update stability burden.
-/
def routingUnresolved : ClaimProfile -> UpdateClass -> Bool
  | .unresolved, _ => true
  | .fitOnly, .unresolved => false
  | _, .unresolved => true
  | _, _ => false

/-! --------------------------------------------------------------------------
Burden liveness
---------------------------------------------------------------------------- -/

def live (c : ClaimProfile) (u : UpdateClass) : Burden -> Bool
  | .descriptionProtection =>
      if routingUnresolved c u then
        false
      else
        claimsDescriptionProtection c && hasDescriptionUpdate u
  | .successorLineage =>
      if routingUnresolved c u then
        false
      else
        claimsSuccessorContinuity c && hasPhysicalSuccessor u
  | .successorBaselineProtection =>
      if routingUnresolved c u then
        false
      else
        claimsSuccessorBaselineProtection c && hasPhysicalSuccessor u

/-! --------------------------------------------------------------------------
Frozen routing theorems
---------------------------------------------------------------------------- -/

/-- Pure description updates never activate the PAA-lineage burden by themselves. -/
theorem description_update_does_not_activate_successor_lineage
    (c : ClaimProfile)
    (d : DescriptionUpdate) :
    live c (.description d) .successorLineage = false := by
  cases c <;> rfl

/-- A pure physical successor does not activate description-protection by itself. -/
theorem physical_successor_does_not_activate_description_protection
    (c : ClaimProfile) :
    live c .physicalSuccessor .descriptionProtection = false := by
  cases c <;> rfl

/-- Successor baseline protection cannot be live without successor lineage. -/
theorem baseline_protection_live_implies_lineage_live
    (c : ClaimProfile)
    (u : UpdateClass)
    (h :
      live c u .successorBaselineProtection = true) :
    live c u .successorLineage = true := by
  cases c <;> cases u <;>
    simp [
      live,
      routingUnresolved,
      claimsSuccessorContinuity,
      claimsSuccessorBaselineProtection,
      hasPhysicalSuccessor
    ] at h ⊢

/-- Full protection under a mixed perturbative case activates all three burdens. -/
theorem full_protection_mixed_perturbative_all_live :
    live
        .fullProtection
        (.mixed .perturbativeRefinement)
        .descriptionProtection = true
    ∧
    live
        .fullProtection
        (.mixed .perturbativeRefinement)
        .successorLineage = true
    ∧
    live
        .fullProtection
        (.mixed .perturbativeRefinement)
        .successorBaselineProtection = true := by
  decide

/-- Full protection under a mixed matching case activates all three burdens. -/
theorem full_protection_mixed_matching_all_live :
    live
        .fullProtection
        (.mixed .resolutionMatching)
        .descriptionProtection = true
    ∧
    live
        .fullProtection
        (.mixed .resolutionMatching)
        .successorLineage = true
    ∧
    live
        .fullProtection
        (.mixed .resolutionMatching)
        .successorBaselineProtection = true := by
  decide

/-! --------------------------------------------------------------------------
Case packet and effective burden status
---------------------------------------------------------------------------- -/

/--
`rawStatus` is populated from the scientific adjudication.

The routing layer normalizes a raw NOT-LIVE on a genuinely live burden to
UNRESOLVED rather than permitting NOT-LIVE to hide a live burden.
-/
structure CasePacket where
  claim : ClaimProfile
  update : UpdateClass
  rawStatus : Burden -> BurdenStatus

def effectiveStatus (p : CasePacket) (b : Burden) : BurdenStatus :=
  if routingUnresolved p.claim p.update then
    .unresolved
  else if live p.claim p.update b then
    match p.rawStatus b with
    | .notLive => .unresolved
    | s => s
  else
    .notLive

/-! --------------------------------------------------------------------------
Status predicates
---------------------------------------------------------------------------- -/

def isFail : BurdenStatus -> Bool
  | .fail => true
  | _ => false

def isUnresolved : BurdenStatus -> Bool
  | .unresolved => true
  | _ => false

def isPass : BurdenStatus -> Bool
  | .pass => true
  | _ => false

def anyFail (p : CasePacket) : Bool :=
  isFail (effectiveStatus p .descriptionProtection)
  || isFail (effectiveStatus p .successorLineage)
  || isFail (effectiveStatus p .successorBaselineProtection)

def anyUnresolved (p : CasePacket) : Bool :=
  isUnresolved (effectiveStatus p .descriptionProtection)
  || isUnresolved (effectiveStatus p .successorLineage)
  || isUnresolved (effectiveStatus p .successorBaselineProtection)

def anyPass (p : CasePacket) : Bool :=
  isPass (effectiveStatus p .descriptionProtection)
  || isPass (effectiveStatus p .successorLineage)
  || isPass (effectiveStatus p .successorBaselineProtection)

/-! --------------------------------------------------------------------------
Frozen case disposition
---------------------------------------------------------------------------- -/

/--
Precedence:
FAIL > UNRESOLVED > PASS > NOT LIVE.

PASS therefore requires at least one live discharged burden.
All-NOT-LIVE never becomes PASS.
-/
def disposition (p : CasePacket) : BurdenStatus :=
  if anyFail p then
    .fail
  else if anyUnresolved p then
    .unresolved
  else if anyPass p then
    .pass
  else
    .notLive

/-! --------------------------------------------------------------------------
Core firewalls
---------------------------------------------------------------------------- -/

/-- A live burden cannot be hidden by raw NOT-LIVE; it becomes UNRESOLVED. -/
theorem live_raw_notLive_becomes_unresolved
    (p : CasePacket)
    (b : Burden)
    (hRoute :
      routingUnresolved p.claim p.update = false)
    (hLive :
      live p.claim p.update b = true)
    (hRaw :
      p.rawStatus b = .notLive) :
    effectiveStatus p b = .unresolved := by
  simp [effectiveStatus, hRoute, hLive, hRaw]

/-- Fit-only plus an unresolved update remains NOT LIVE, not UNRESOLVED. -/
theorem fit_only_unresolved_update_not_live
    (raw : Burden -> BurdenStatus) :
    disposition
      {
        claim := .fitOnly
        update := .unresolved
        rawStatus := raw
      } = .notLive := by
  rfl

/-- An unresolved non-fit claim cannot be machine-promoted to PASS. -/
theorem unresolved_description_claim_is_unresolved
    (raw : Burden -> BurdenStatus) :
    disposition
      {
        claim := .descriptionProtection
        update := .unresolved
        rawStatus := raw
      } = .unresolved := by
  rfl

/--
Mixed full protection is conjunctive at the case level:
a failure in the PAA-lineage branch defeats overall PASS even if the
description-protection and baseline-response burdens pass.
-/
theorem mixed_full_lineage_fail_defeats_pass :
    disposition
      {
        claim := .fullProtection
        update := .mixed .resolutionMatching
        rawStatus :=
          fun b =>
            match b with
            | .descriptionProtection => .pass
            | .successorLineage => .fail
            | .successorBaselineProtection => .pass
      } = .fail := by
  rfl

/--
A successor-continuity claim can PASS its live PAA-lineage burden without
making any successor-baseline-protection claim.
-/
theorem continuity_pass_does_not_upgrade_to_baseline_protection :
    let p : CasePacket :=
      {
        claim := .successorContinuity
        update := .physicalSuccessor
        rawStatus :=
          fun b =>
            match b with
            | .descriptionProtection => .notLive
            | .successorLineage => .pass
            | .successorBaselineProtection => .notLive
      }
    disposition p = .pass
    ∧ effectiveStatus p .successorBaselineProtection = .notLive := by
  decide

/-! --------------------------------------------------------------------------
Hooks to unchanged Universal Kernel
---------------------------------------------------------------------------- -/

/--
Branch-S successor accounting reuses the kernel's PAA source guard directly.
The domain adapter supplies the physical successor relation.
-/
def PAAValidContinuation
    {State : Type}
    (a : PAA.AuthorizationRecord State)
    (step : PAA.Successor State)
    (c : PAA.ContinuationClaim State) : Prop :=
  PAA.SourceValid a step c

/--
Branch-R remains downstream of Authorization and PAA-compatible origin lineage.
The actual description surfaces / presentations are supplied later through
Recognition.World; this first routing adapter does not manufacture them.
-/
def RecognitionReady
    {State Surface Content Presentation : Type}
    (w : Recognition.World State Surface Content Presentation) : Prop :=
  Recognition.UpstreamReady w

/-! --------------------------------------------------------------------------
Non-claims
---------------------------------------------------------------------------- -/

/-
Machine-clean routing would establish only:
* the frozen liveness matrix;
* branch separation;
* mixed-route conjunction;
* unresolved routing;
* four-state disposition precedence;
* no false PASS from NOT-LIVE;
* no successor baseline protection without successor lineage;
* and compatibility hooks to the unchanged kernel.

It would NOT establish that any physical premise is true.
-/

end CosmologicalConstantStabilityRouting
end StructuralFlow


/-!
===============================================================================
COSMOLOGICAL-CONSTANT STABILITY ROUTING ADAPTER v0.2 — APPEND BLOCK
===============================================================================

APPEND ORDER
------------
1. Structural_Flow_Universal_Kernel_v1.0.lean
2. Cosmological_Constant_Stability_Routing_Adapter_v0.1.lean
3. THIS BLOCK

ROLE
----
Bind the already-machine-clean v0.1 routing table to the exact Universal Kernel
structures used by the two live structural branches:

Branch R:
  Recognition.World
  + Recognition.UpstreamReady
  + Recognition.Recognizes

Branch L:
  PAA.AuthorizationRecord
  + PAA.Successor
  + PAA.AccountedReachable
  + PAA.ContinuationClaim

Branch B remains domain-owned and is encoded only as a criterion layered on top
of a valid Branch-L certificate.

This block does NOT decide physical premises.
It does NOT calculate Lambda.
It does NOT perform QFT, EFT matching, or phase-transition physics.
It introduces no Universal Kernel change.
===============================================================================
-/

namespace StructuralFlow
namespace CosmologicalConstantStabilityRouting

/-! --------------------------------------------------------------------------
1. Exact Recognition.World bridge
---------------------------------------------------------------------------- -/

/--
Extract the exact PAA authorization record already represented inside a
Recognition.World.
-/
def recognitionAuthorization
    {State Surface Content Presentation : Type}
    (w : Recognition.World State Surface Content Presentation) :
    PAA.AuthorizationRecord State where
  pre := w.pre
  post := w.post
  changed := w.changed

/--
Extract the exact continuation claim already represented inside a
Recognition.World.
-/
def recognitionContinuation
    {State Surface Content Presentation : Type}
    (w : Recognition.World State Surface Content Presentation) :
    PAA.ContinuationClaim State where
  source := w.continuationSource

/--
Kernel fact:
Recognition upstream readiness already contains PAA-compatible origin lineage.

Important semantic firewall:
this is the lineage condition required BEFORE Recognition.
It does NOT classify the description update itself as a physical successor.
-/
theorem recognition_upstream_supplies_paa_source_valid
    {State Surface Content Presentation : Type}
    {w : Recognition.World State Surface Content Presentation}
    (h : Recognition.UpstreamReady w) :
    PAA.SourceValid
      (recognitionAuthorization w)
      w.successor
      (recognitionContinuation w) := by
  unfold PAA.SourceValid
  have hPAA : Recognition.PAACompatible w := h.2
  unfold Recognition.PAACompatible at hPAA
  exact hPAA

/-! --------------------------------------------------------------------------
2. Branch-R kernel binding
---------------------------------------------------------------------------- -/

/--
A machine certificate for a successful Recognition-side transport task.

Physics / the scientific anchor supplies the actual meaning of:
* the two description surfaces;
* the lawful variation;
* the transport relation;
* and the binding content.

Lean checks only that the populated Recognition world satisfies the kernel
conditions.
-/
structure DescriptionKernelBinding
    (State Surface Content Presentation : Type) where
  world : Recognition.World State Surface Content Presentation
  upstreamReady : Recognition.UpstreamReady world
  recognizes : Recognition.Recognizes world

/-- A Branch-R kernel binding reaches the kernel's same-binding endpoint. -/
theorem description_binding_reaches_endpoint
    {State Surface Content Presentation : Type}
    (b : DescriptionKernelBinding State Surface Content Presentation) :
    Recognition.SameBindingTransportEndpoint b.world := by
  exact Recognition.recognized_authorized_content_reaches_endpoint
    b.upstreamReady.1
    b.recognizes

/--
The Recognition binding preserves its required upstream PAA compatibility
without turning the description update into a Branch-L successor claim.
-/
theorem description_binding_is_upstream_paa_compatible
    {State Surface Content Presentation : Type}
    (b : DescriptionKernelBinding State Surface Content Presentation) :
    Recognition.PAACompatible b.world := by
  exact b.upstreamReady.2

/-! --------------------------------------------------------------------------
3. Branch-L kernel binding
---------------------------------------------------------------------------- -/

/--
A machine certificate for a successful physical-successor lineage.

The domain supplies the lawful successor relation.
Lean checks only that the claimed continuation source is actually reachable
from the authorized post-state through that relation.
-/
structure SuccessorKernelBinding (State : Type) where
  authorization : PAA.AuthorizationRecord State
  successor : PAA.Successor State
  continuation : PAA.ContinuationClaim State
  accounted :
    PAA.AccountedReachable
      successor
      authorization.post
      continuation.source

/-- The exact kernel SourceValid predicate follows from accounted reachability. -/
theorem successor_binding_source_valid
    {State : Type}
    (b : SuccessorKernelBinding State) :
    PAA.SourceValid b.authorization b.successor b.continuation := by
  unfold PAA.SourceValid
  exact b.accounted

/--
A minimal warrant containing exactly the continuation represented by the
Branch-L binding.
-/
def successorBindingWarrant
    {State : Type}
    (b : SuccessorKernelBinding State) :
    PAA.ContinuationClaim State → Prop :=
  fun c => c = b.continuation

/-- The singleton warrant respects the kernel PAA guard. -/
theorem successor_binding_respects_paa
    {State : Type}
    (b : SuccessorKernelBinding State) :
    PAA.RespectsPAA
      b.authorization
      b.successor
      (successorBindingWarrant b) := by
  intro c hW
  cases hW
  exact successor_binding_source_valid b

/-- Therefore the bound successor claim cannot contain a kernel free reset. -/
theorem successor_binding_excludes_free_reset
    {State : Type}
    (b : SuccessorKernelBinding State) :
    ¬ PAA.FreeResetViolation
        b.authorization
        b.successor
        (successorBindingWarrant b) := by
  exact PAA.paa_excludes_free_reset
    b.authorization
    b.successor
    (successorBindingWarrant b)
    (successor_binding_respects_paa b)

/-! --------------------------------------------------------------------------
4. Routing status + kernel witness certificates
---------------------------------------------------------------------------- -/

/--
A complete Branch-R PASS certificate requires BOTH:
* the frozen routing table says the R burden is live and PASS;
* an exact Recognition kernel witness discharges the structural transport task.
-/
structure DescriptionPassBinding
    (State Surface Content Presentation : Type) where
  packet : CasePacket
  liveR :
    live packet.claim packet.update .descriptionProtection = true
  passR :
    effectiveStatus packet .descriptionProtection = .pass
  kernel :
    DescriptionKernelBinding State Surface Content Presentation

/--
A complete Branch-L PASS certificate requires BOTH:
* the frozen routing table says the lineage burden is live and PASS;
* an exact PAA accounted-successor witness discharges the lineage task.
-/
structure SuccessorLineagePassBinding (State : Type) where
  packet : CasePacket
  liveL :
    live packet.claim packet.update .successorLineage = true
  passL :
    effectiveStatus packet .successorLineage = .pass
  kernel :
    SuccessorKernelBinding State

/--
Branch B is deliberately downstream of Branch L.

A successful post-successor baseline-protection certificate cannot even be
constructed without a successful lineage certificate for the SAME CasePacket.
The baseline object and criterion remain domain-owned.
-/
structure SuccessorBaselineProtectionPassBinding
    (State Baseline : Type) where
  lineage : SuccessorLineagePassBinding State
  liveB :
    live
      lineage.packet.claim
      lineage.packet.update
      .successorBaselineProtection = true
  passB :
    effectiveStatus
      lineage.packet
      .successorBaselineProtection = .pass
  baseline : Baseline
  criterion : Baseline → Prop
  criterionSatisfied : criterion baseline

/--
The Branch-B certificate structurally carries a Branch-L PAA-valid successor.
-/
theorem baseline_protection_binding_has_valid_lineage
    {State Baseline : Type}
    (b : SuccessorBaselineProtectionPassBinding State Baseline) :
    PAA.SourceValid
      b.lineage.kernel.authorization
      b.lineage.kernel.successor
      b.lineage.kernel.continuation := by
  exact successor_binding_source_valid b.lineage.kernel

/-! --------------------------------------------------------------------------
5. Concrete firewall packets
---------------------------------------------------------------------------- -/

def descriptionOnlyPassPacket
    (d : DescriptionUpdate) : CasePacket where
  claim := .descriptionProtection
  update := .description d
  rawStatus :=
    fun b =>
      match b with
      | .descriptionProtection => .pass
      | .successorLineage => .notLive
      | .successorBaselineProtection => .notLive

def continuityOnlyPassPacket : CasePacket where
  claim := .successorContinuity
  update := .physicalSuccessor
  rawStatus :=
    fun b =>
      match b with
      | .descriptionProtection => .notLive
      | .successorLineage => .pass
      | .successorBaselineProtection => .notLive

def fullMixedPassPacket
    (d : DescriptionUpdate) : CasePacket where
  claim := .fullProtection
  update := .mixed d
  rawStatus :=
    fun _ => .pass

/-! --------------------------------------------------------------------------
6. Firewall theorem A:
   Recognition PASS cannot masquerade as a PAA successor PASS
---------------------------------------------------------------------------- -/

/--
Even with a real kernel Recognition success AND its required upstream
PAA-compatible origin lineage, a pure description-update case keeps the
successor-lineage burden NOT LIVE.

This is the formal separation:
Recognition's upstream PAA compatibility
≠
the description update becoming a physical successor.
-/
theorem recognition_pass_is_not_successor_pass
    {State Surface Content Presentation : Type}
    (d : DescriptionUpdate)
    (k : DescriptionKernelBinding State Surface Content Presentation) :
    Recognition.SameBindingTransportEndpoint k.world
    ∧ Recognition.PAACompatible k.world
    ∧ effectiveStatus
        (descriptionOnlyPassPacket d)
        .descriptionProtection = .pass
    ∧ effectiveStatus
        (descriptionOnlyPassPacket d)
        .successorLineage = .notLive := by
  refine ⟨
    description_binding_reaches_endpoint k,
    description_binding_is_upstream_paa_compatible k,
    ?_,
    ?_
  ⟩
  · cases d <;> rfl
  · cases d <;> rfl

/-! --------------------------------------------------------------------------
7. Firewall theorem B:
   PAA-valid successor PASS cannot masquerade as baseline protection
---------------------------------------------------------------------------- -/

/--
A genuine kernel-valid PAA successor can PASS the successor-continuity claim
while post-successor baseline protection remains NOT LIVE.

Thus:
PAA-valid continuation
≠
cosmological-constant stability.
-/
theorem paa_valid_successor_is_not_baseline_protection
    {State : Type}
    (k : SuccessorKernelBinding State) :
    PAA.SourceValid k.authorization k.successor k.continuation
    ∧ effectiveStatus
        continuityOnlyPassPacket
        .successorLineage = .pass
    ∧ effectiveStatus
        continuityOnlyPassPacket
        .successorBaselineProtection = .notLive := by
  exact ⟨
    successor_binding_source_valid k,
    rfl,
    rfl
  ⟩

/-! --------------------------------------------------------------------------
8. Mixed route requires two distinct kernel bindings
---------------------------------------------------------------------------- -/

/--
Machine representation of a fully protected mixed case.

The Recognition witness and the PAA successor witness remain separate fields.
Neither can substitute for the other.
-/
structure MixedFullKernelBinding
    (RState Surface Content Presentation SState Baseline : Type) where
  description :
    DescriptionKernelBinding RState Surface Content Presentation
  successor :
    SuccessorKernelBinding SState
  baseline : Baseline
  criterion : Baseline → Prop
  criterionSatisfied : criterion baseline

/--
For the frozen full-protection mixed packet, all three scientific burdens are
live and PASS, while the machine evidence still consists of separate
Recognition and PAA witnesses plus the domain-owned baseline criterion.
-/
theorem mixed_full_binding_keeps_branches_distinct
    {RState Surface Content Presentation SState Baseline : Type}
    (d : DescriptionUpdate)
    (k :
      MixedFullKernelBinding
        RState Surface Content Presentation SState Baseline) :
    Recognition.SameBindingTransportEndpoint k.description.world
    ∧ PAA.SourceValid
        k.successor.authorization
        k.successor.successor
        k.successor.continuation
    ∧ effectiveStatus
        (fullMixedPassPacket d)
        .descriptionProtection = .pass
    ∧ effectiveStatus
        (fullMixedPassPacket d)
        .successorLineage = .pass
    ∧ effectiveStatus
        (fullMixedPassPacket d)
        .successorBaselineProtection = .pass := by
  refine ⟨
    description_binding_reaches_endpoint k.description,
    successor_binding_source_valid k.successor,
    ?_,
    ?_,
    ?_
  ⟩
  · cases d <;> rfl
  · cases d <;> rfl
  · cases d <;> rfl

/-! --------------------------------------------------------------------------
9. Machine-ceiling statement
---------------------------------------------------------------------------- -/

/-
If this append block elaborates cleanly, it establishes ONLY the following
conditional machine facts:

1. Branch R is genuinely bound to Recognition.World / Recognizes.
2. Branch L is genuinely bound to AuthorizationRecord + Successor
   + AccountedReachable.
3. Recognition's own upstream PAA compatibility does not activate a physical
   successor route in a description-only case.
4. A PAA-valid successor does not by itself license post-transition baseline
   protection.
5. Branch B is structurally downstream of a valid Branch-L certificate.
6. A mixed case keeps Recognition evidence and PAA evidence separate.
7. No Universal Kernel modification is required by this binding.

It does NOT establish any physical premise or empirical truth.
-/


/-!
===============================================================================
COSMOLOGICAL-CONSTANT STABILITY ROUTING ADAPTER v0.3 — SEMANTIC LAYER
===============================================================================

ROLE
----
This layer DOES NOT change the v0.1 routing table or the v0.2 kernel bindings.

It adds only the scientific-state distinctions earned after adversarial pressure
and real-mechanism population:

* PASS provenance is separate from empirical discrimination;
* protection non-vacuity is separate from channel equivalence;
* NOT LIVE is separate from OUT OF DOMAIN and NOT IDENTIFIABLE;
* NOT IDENTIFIABLE is evaluated relative to a frozen channel set;
* branch evidence may share one structural identity;
* profile-level scientific results remain profile-labelled;
* structural protection never implies empirical discrimination.

Physics owns every populated premise.
Lean checks only the encoded conditional semantics.
No Universal Kernel modification is introduced.
===============================================================================
-/

/-! --------------------------------------------------------------------------
10. PASS provenance
---------------------------------------------------------------------------- -/

/--
PASS provenance is multi-valued: more than one field may be true.
For example, an analytic identity may be confirmed by a computation.
-/
structure PassProvenance where
  structural : Bool
  computational : Bool
  empirical : Bool
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
11. Program-level protection non-vacuity
---------------------------------------------------------------------------- -/

inductive ProtectionNonVacuity where
  | nonvacuous
  | fitOnly
  | open
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
12. Channel relation / empirical observability
---------------------------------------------------------------------------- -/

/--
`constraintFixedChannelEquivalent` means:
M fixes the relevant datum through its own equations / constraint, but the
frozen channel set cannot distinguish the resulting prediction from the
registered reference model with one fitted datum.

This is deliberately NOT `fitOnly`.
-/
inductive ChannelRelation where
  | discriminating
  | constraintFixedChannelEquivalent
  | belowSensitivity
  | forwardModelOpen
  | channelOpen
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
13. Evidence-dependence ledger
---------------------------------------------------------------------------- -/

inductive EvidenceDependence where
  | independent
  | partiallyShared
  | sameStructuralIdentity
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
14. Admission / applicability / execution separation
---------------------------------------------------------------------------- -/

inductive AdmissionBlocker where
  | sourceOpen
  | shiftOpen
  | bridgeOpen
  | protectedFunctionalOpen
  | freeDatumLedgerOpen
  deriving DecidableEq, Repr

inductive AdmissionState where
  | admitted
  | notAdmitted (reason : AdmissionBlocker)
  deriving DecidableEq, Repr

/--
Applicability states are theory / laboratory / channel-set states.

`notLive` means only: no registered claim at this branch / scope.
`outOfDomain` means the proposed laboratory lies outside M's domain.
`notIdentifiable` means exact structural degeneracy over the frozen channel set.
-/
inductive ApplicabilityState where
  | live
  | notLive
  | outOfDomain
  | notIdentifiable
  deriving DecidableEq, Repr

inductive ExecutionBlocker where
  | belowSensitivity
  | forwardModelOpen
  | insufficientData
  | theoryDependenceUnmodeled
  | channelOpen
  deriving DecidableEq, Repr

inductive ExecutionState where
  | notRun
  | pass
  | fail
  | unresolved (reason : ExecutionBlocker)
  deriving DecidableEq, Repr

/-! --------------------------------------------------------------------------
15. Channel-scoped semantic packet
---------------------------------------------------------------------------- -/

/--
`ChannelSet` is intentionally domain-owned.
It may be a concrete list, manifest id, record, or any other scientific object.
The adapter only preserves which frozen channel set the disposition belongs to.
-/
structure SemanticPacket (ChannelSet : Type) where
  channelSet : ChannelSet
  admission : AdmissionState
  applicability : ApplicabilityState
  rawExecution : ExecutionState
  provenance : PassProvenance
  protection : ProtectionNonVacuity
  channelRelation : ChannelRelation
  evidenceDependence : EvidenceDependence

/--
Only an admitted, LIVE case may produce an execution result.
Everything else normalizes to `notRun` rather than silently becoming PASS.
-/
def executionAllowed
    (a : AdmissionState)
    (s : ApplicabilityState) : Bool :=
  match a, s with
  | .admitted, .live => true
  | _, _ => false

/--
This normalization is semantic only.
It does not determine whether the scientific admission / applicability premise
is physically correct.
-/
def effectiveExecution
    {ChannelSet : Type}
    (p : SemanticPacket ChannelSet) : ExecutionState :=
  if executionAllowed p.admission p.applicability then
    p.rawExecution
  else
    .notRun

/-! --------------------------------------------------------------------------
16. Semantic predicates
---------------------------------------------------------------------------- -/

/--
A structural protection PASS requires:
* admitted + live;
* effective execution PASS;
* structural provenance;
* non-vacuous protection.

It deliberately does NOT require channel discrimination.
-/
def StructuralProtectionPass
    {ChannelSet : Type}
    (p : SemanticPacket ChannelSet) : Prop :=
  effectiveExecution p = .pass
  ∧ p.provenance.structural = true
  ∧ p.protection = .nonvacuous

/--
An empirical discrimination PASS additionally requires:
* empirical provenance;
* a discriminating frozen channel set.
-/
def EmpiricalDiscriminationPass
    {ChannelSet : Type}
    (p : SemanticPacket ChannelSet) : Prop :=
  effectiveExecution p = .pass
  ∧ p.provenance.empirical = true
  ∧ p.channelRelation = .discriminating

/-! --------------------------------------------------------------------------
17. Applicability firewalls
---------------------------------------------------------------------------- -/

/-- Exact structural non-identifiability cannot normalize to execution PASS. -/
theorem not_identifiable_blocks_execution_pass
    {ChannelSet : Type}
    (p : SemanticPacket ChannelSet)
    (h : p.applicability = .notIdentifiable) :
    effectiveExecution p ≠ .pass := by
  unfold effectiveExecution executionAllowed
  rw [h]
  simp

/-- OUT OF DOMAIN cannot normalize to execution PASS. -/
theorem out_of_domain_blocks_execution_pass
    {ChannelSet : Type}
    (p : SemanticPacket ChannelSet)
    (h : p.applicability = .outOfDomain) :
    effectiveExecution p ≠ .pass := by
  unfold effectiveExecution executionAllowed
  rw [h]
  simp

/-- NOT LIVE cannot normalize to execution PASS. -/
theorem not_live_blocks_execution_pass
    {ChannelSet : Type}
    (p : SemanticPacket ChannelSet)
    (h : p.applicability = .notLive) :
    effectiveExecution p ≠ .pass := by
  unfold effectiveExecution executionAllowed
  rw [h]
  simp

/-- A blocked admission cannot normalize to execution PASS. -/
theorem not_admitted_blocks_execution_pass
    {ChannelSet : Type}
    (p : SemanticPacket ChannelSet)
    (reason : AdmissionBlocker)
    (h : p.admission = .notAdmitted reason) :
    effectiveExecution p ≠ .pass := by
  unfold effectiveExecution executionAllowed
  rw [h]
  cases p.applicability <;> simp

/-! --------------------------------------------------------------------------
18. Structural protection != empirical discrimination
---------------------------------------------------------------------------- -/

/--
Canonical semantic fixture:
protection is structurally non-vacuous and PASS,
but the frozen channel set is constraint-fixed / channel-equivalent to fit.

This is the exact Round-4 firewall.
-/
def structuralButChannelEquivalentPacket : SemanticPacket Unit where
  channelSet := ()
  admission := .admitted
  applicability := .live
  rawExecution := .pass
  provenance := {
    structural := true
    computational := false
    empirical := false
  }
  protection := .nonvacuous
  channelRelation := .constraintFixedChannelEquivalent
  evidenceDependence := .sameStructuralIdentity

/--
Machine firewall:
STRUCTURAL PROTECTION PASS
DOES NOT IMPLY
EMPIRICAL DISCRIMINATION PASS.
-/
theorem structural_protection_does_not_imply_empirical_discrimination :
    StructuralProtectionPass structuralButChannelEquivalentPacket
    ∧ ¬ EmpiricalDiscriminationPass structuralButChannelEquivalentPacket := by
  simp [StructuralProtectionPass,
        EmpiricalDiscriminationPass,
        structuralButChannelEquivalentPacket,
        effectiveExecution,
        executionAllowed]

/-- FIT-ONLY cannot satisfy the semantic structural-protection predicate. -/
def fitOnlyStructuralFixture : SemanticPacket Unit where
  channelSet := ()
  admission := .admitted
  applicability := .live
  rawExecution := .pass
  provenance := {
    structural := true
    computational := false
    empirical := false
  }
  protection := .fitOnly
  channelRelation := .channelOpen
  evidenceDependence := .sameStructuralIdentity

theorem fit_only_is_not_structural_protection :
    ¬ StructuralProtectionPass fitOnlyStructuralFixture := by
  simp [StructuralProtectionPass,
        fitOnlyStructuralFixture,
        effectiveExecution,
        executionAllowed]

/-! --------------------------------------------------------------------------
19. Channel-relative non-identifiability
---------------------------------------------------------------------------- -/

/--
The adapter preserves the scientific channel set instead of promoting a
channel-relative result into universal equivalence.
-/
structure NonIdentifiabilityRecord (ChannelSet : Type) where
  channelSet : ChannelSet
  applicability : ApplicabilityState
  isNotIdentifiable : applicability = .notIdentifiable

/--
Two non-identifiability records may lawfully refer to different channel sets.
No theorem equates those channel sets or upgrades either record to universal
observational equivalence.
-/
structure DistinctChannelNonIdentifiability
    (ChannelSetA ChannelSetB : Type) where
  first : NonIdentifiabilityRecord ChannelSetA
  second : NonIdentifiabilityRecord ChannelSetB

/-! --------------------------------------------------------------------------
20. Profile-labelled scientific result
---------------------------------------------------------------------------- -/

/--
The scientific anchor owns the profile-level adjudication.
The adapter preserves the profile label and semantic state faithfully.
-/
structure ProfileResult (ChannelSet : Type) where
  profile : ClaimProfile
  semantics : SemanticPacket ChannelSet

/-! --------------------------------------------------------------------------
21. Evidence dependence does not erase branch identity
---------------------------------------------------------------------------- -/

/--
Two branches may legitimately pass under the same structural identity.
This records shared evidence without collapsing the branches themselves.
-/
structure SharedStructuralBranchEvidence where
  firstBranch : DescriptionUpdate
  secondBranch : DescriptionUpdate
  dependence : EvidenceDependence
  sameIdentity : dependence = .sameStructuralIdentity

/--
Perturbative refinement and EFT matching remain distinct registered update
classes even when their PASS proofs share one structural identity.
-/
def r1r2SharedStructuralEvidence : SharedStructuralBranchEvidence where
  firstBranch := .perturbativeRefinement
  secondBranch := .resolutionMatching
  dependence := .sameStructuralIdentity
  sameIdentity := rfl

/-! --------------------------------------------------------------------------
22. v0.3 machine ceiling
---------------------------------------------------------------------------- -/

/-
If this entire consolidated v0.3 file elaborates cleanly, it establishes ONLY:

1. The already-machine-clean v0.1 routing semantics still stand.
2. The already-machine-clean v0.2 Recognition / PAA kernel bindings still stand.
3. PASS provenance can be represented separately from empirical discrimination.
4. Protection non-vacuity can be represented separately from channel relation.
5. NOT LIVE, OUT OF DOMAIN, and NOT IDENTIFIABLE are distinct applicability
   states.
6. A non-live / out-of-domain / not-identifiable case cannot normalize to an
   execution PASS.
7. Channel-relative NOT IDENTIFIABLE preserves its frozen channel set.
8. Shared structural evidence across R1/R2 does not collapse their branch ids.
9. Structural protection PASS does not imply empirical discrimination PASS.
10. FIT-ONLY cannot satisfy the semantic structural-protection predicate.
11. No Universal Kernel modification is required by these distinctions.

It does NOT establish:
* that any cosmological-constant mechanism is physically correct;
* that any source object is physically admitted;
* that any channel set is experimentally adequate;
* that any comparator is scientifically complete;
* that sequestering or any named mechanism is true;
* or that empirical discrimination has occurred.
-/

/-! --------------------------------------------------------------------------
23. v0.4 physical-successor experiment ledger
---------------------------------------------------------------------------- -/

/--
Experiment seats reuse the Universal Kernel's existing three-state burden
Disposition. `none` means the seat is not required / not live for the
registered route. A required but unresolved seat MUST be `some .open`.
-/
abbrev ExperimentDisposition :=
  StructuralFlow.UniversalTranslationContract.Disposition

inductive SuccessorExperimentRoute where
  | epochLocal
  | historicalProtectedTransition
  | wholeHistory
  deriving DecidableEq, Repr

/-- Domain-owned S_m experiment burdens earned by the empirical-closure audit. -/
inductive SuccessorExperimentBurden where
  | realChange
  | protectedSectorMembership
  | piRelevantChange
  | mechanismApplicability
  | inheritedTheoryData
  | variationConnection
  | falsificationConnection
  | freeDatumStability
  | completionIdentity
  | completionViability
  | historyClosure
  | forwardModel
  | channelSet
  | fittedComparator
  | matchedUnprotectedComparator
  | alternativeCoverage
  | mappability
  | degeneracyTest
  | sensitivity
  | dataAdequacy
  | dataConsistency
  | resultFreeze
  deriving DecidableEq, Repr

/--
Route-specific audit ledger. Physics owns which seats are required and their
scientific disposition. Lean only preserves the supplied record.
-/
structure SuccessorExperimentLedger where
  route : SuccessorExperimentRoute
  seat : SuccessorExperimentBurden -> Option ExperimentDisposition

/-- Required seats close only when discharged; `none` is not required. -/
def ExperimentSeatClosed
    (l : SuccessorExperimentLedger)
    (b : SuccessorExperimentBurden) : Prop :=
  match l.seat b with
  | none => True
  | some .discharged => True
  | some .violated => False
  | some .open => False

/--
The first eight S_m burdens are constitutive of a CCP physical-successor test.
They may be DISCHARGED / VIOLATED / OPEN, but may not be hidden as `none`.
-/
def CoreSuccessorSeatsDeclared
    (l : SuccessorExperimentLedger) : Prop :=
  l.seat .realChange ≠ none
  ∧ l.seat .protectedSectorMembership ≠ none
  ∧ l.seat .piRelevantChange ≠ none
  ∧ l.seat .mechanismApplicability ≠ none
  ∧ l.seat .inheritedTheoryData ≠ none
  ∧ l.seat .variationConnection ≠ none
  ∧ l.seat .falsificationConnection ≠ none
  ∧ l.seat .freeDatumStability ≠ none

inductive CoreSuccessorBurden : SuccessorExperimentBurden -> Prop where
  | realChange : CoreSuccessorBurden .realChange
  | protectedSectorMembership : CoreSuccessorBurden .protectedSectorMembership
  | piRelevantChange : CoreSuccessorBurden .piRelevantChange
  | mechanismApplicability : CoreSuccessorBurden .mechanismApplicability
  | inheritedTheoryData : CoreSuccessorBurden .inheritedTheoryData
  | variationConnection : CoreSuccessorBurden .variationConnection
  | falsificationConnection : CoreSuccessorBurden .falsificationConnection
  | freeDatumStability : CoreSuccessorBurden .freeDatumStability

/--
Positive closure of all machine-required seats in this supplied ledger snapshot.
This is not, by itself, a chronological acquisition-go decision or empirical
success certificate.
-/
def ExperimentReadyForEmpiricalRun
    (l : SuccessorExperimentLedger) : Prop :=
  CoreSuccessorSeatsDeclared l
  ∧ forall b, ExperimentSeatClosed l b

theorem core_successor_burden_declared
    (l : SuccessorExperimentLedger)
    {b : SuccessorExperimentBurden}
    (hb : CoreSuccessorBurden b)
    (hready : ExperimentReadyForEmpiricalRun l) :
    l.seat b ≠ none := by
  rcases hready.1 with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  cases hb with
  | realChange => exact h1
  | protectedSectorMembership => exact h2
  | piRelevantChange => exact h3
  | mechanismApplicability => exact h4
  | inheritedTheoryData => exact h5
  | variationConnection => exact h6
  | falsificationConnection => exact h7
  | freeDatumStability => exact h8

theorem missing_core_successor_seat_blocks_empirical_readiness
    (l : SuccessorExperimentLedger)
    {b : SuccessorExperimentBurden}
    (hb : CoreSuccessorBurden b)
    (h : l.seat b = none) :
    ¬ ExperimentReadyForEmpiricalRun l := by
  intro hready
  exact (core_successor_burden_declared l hb hready) h

theorem open_required_seat_blocks_empirical_readiness
    (l : SuccessorExperimentLedger)
    (b : SuccessorExperimentBurden)
    (h : l.seat b = some .open) :
    ¬ ExperimentReadyForEmpiricalRun l := by
  intro hready
  have hs := hready.2 b
  simp [ExperimentSeatClosed, h] at hs

theorem violated_required_seat_blocks_empirical_readiness
    (l : SuccessorExperimentLedger)
    (b : SuccessorExperimentBurden)
    (h : l.seat b = some .violated) :
    ¬ ExperimentReadyForEmpiricalRun l := by
  intro hready
  have hs := hready.2 b
  simp [ExperimentSeatClosed, h] at hs

/--
Ledger provenance and terminal CCP semantics are intentionally separate.
The adapter does not infer physical truth from the ledger.
-/
structure SuccessorExperimentCase (ChannelSet : Type) where
  ledger : SuccessorExperimentLedger
  semantics : SemanticPacket ChannelSet

/-! --------------------------------------------------------------------------
24. v0.5 support, license, and routing-consistency layer
---------------------------------------------------------------------------- -/

/-- Outcome-independent support for a positive S_m structural-protection claim. -/
def StructuralProtectionSupportReady
    (l : SuccessorExperimentLedger) : Prop :=
  ExperimentReadyForEmpiricalRun l
  ∧ l.seat .resultFreeze = some .discharged

/-- Outcome-independent support required for positive empirical discrimination. -/
def EmpiricalDiscriminationSupportReady
    (l : SuccessorExperimentLedger) : Prop :=
  ExperimentReadyForEmpiricalRun l
  ∧ l.seat .forwardModel = some .discharged
  ∧ l.seat .channelSet = some .discharged
  ∧ l.seat .fittedComparator = some .discharged
  ∧ l.seat .alternativeCoverage = some .discharged
  ∧ l.seat .mappability = some .discharged
  ∧ l.seat .degeneracyTest = some .discharged
  ∧ l.seat .sensitivity = some .discharged
  ∧ l.seat .dataAdequacy = some .discharged
  ∧ l.seat .dataConsistency = some .discharged
  ∧ l.seat .resultFreeze = some .discharged

/--
Outcome-independent support for a scoped exact-non-identification claim.
The exact mapping / degeneracy outcome remains domain-owned.
-/
def ExactNonIdentificationSupportReady
    (l : SuccessorExperimentLedger) : Prop :=
  ExperimentReadyForEmpiricalRun l
  ∧ l.seat .forwardModel = some .discharged
  ∧ l.seat .channelSet = some .discharged
  ∧ l.seat .fittedComparator = some .discharged
  ∧ l.seat .mappability = some .discharged
  ∧ l.seat .degeneracyTest = some .discharged
  ∧ l.seat .resultFreeze = some .discharged

/-- All required seats except one selected burden are closed. -/
def ExperimentClosedExcept
    (l : SuccessorExperimentLedger)
    (skip : SuccessorExperimentBurden) : Prop :=
  forall b, b ≠ skip -> ExperimentSeatClosed l b

/--
Support for a domain-supplied BELOW SENSITIVITY result. All other honestly
required burdens must already be closed, and sensitivity itself is VIOLATED.
-/
def BelowSensitivitySupportReady
    (l : SuccessorExperimentLedger) : Prop :=
  CoreSuccessorSeatsDeclared l
  ∧ ExperimentClosedExcept l .sensitivity
  ∧ l.seat .forwardModel = some .discharged
  ∧ l.seat .channelSet = some .discharged
  ∧ l.seat .fittedComparator = some .discharged
  ∧ l.seat .mappability = some .discharged
  ∧ l.seat .degeneracyTest = some .discharged
  ∧ l.seat .sensitivity = some .violated
  ∧ l.seat .resultFreeze = some .discharged

/-- Successor lineage is an upstream support burden and must itself PASS. -/
def SuccessorLineageSupportReady
    (p : CasePacket) : Prop :=
  effectiveStatus p .successorLineage = .pass

/-- Successor-baseline protection must at least be a live registered claim. -/
def SuccessorProtectionClaimLive
    (p : CasePacket) : Prop :=
  live p.claim p.update .successorBaselineProtection = true

/--
The two supplied terminal successor-protection representations must agree.
Neither representation is treated as evidence proving the other.
-/
def StructuralProtectionResultAgrees
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet) : Prop :=
  effectiveStatus routing .successorBaselineProtection = .pass
  ∧ StructuralProtectionPass c.semantics

/-- Machine license for a supplied structural-protection adjudication. -/
def StructuralProtectionCaseLicensed
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet) : Prop :=
  SuccessorLineageSupportReady routing
  ∧ SuccessorProtectionClaimLive routing
  ∧ StructuralProtectionSupportReady c.ledger
  ∧ StructuralProtectionResultAgrees routing c

/-- Machine license for a supplied empirical-discrimination adjudication. -/
def EmpiricalDiscriminationCaseLicensed
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet) : Prop :=
  SuccessorLineageSupportReady routing
  ∧ EmpiricalDiscriminationSupportReady c.ledger
  ∧ EmpiricalDiscriminationPass c.semantics

/-- Machine license for a supplied exact-non-identification adjudication. -/
def ExactNonIdentificationCaseLicensed
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet) : Prop :=
  SuccessorLineageSupportReady routing
  ∧ ExactNonIdentificationSupportReady c.ledger
  ∧ c.semantics.admission = .admitted
  ∧ c.semantics.applicability = .notIdentifiable
  ∧ c.semantics.rawExecution = .notRun

/--
Downstream routing consistency only: exact non-identifiability makes sensitivity
non-required. This implication does not establish non-identifiability.
-/
def ExactNonIdentificationRoutingConsistent
    {ChannelSet : Type}
    (c : SuccessorExperimentCase ChannelSet) : Prop :=
  c.semantics.applicability = .notIdentifiable
  -> c.ledger.seat .sensitivity = none

/-- Machine license for a supplied BELOW SENSITIVITY adjudication. -/
def BelowSensitivityCaseLicensed
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet) : Prop :=
  SuccessorLineageSupportReady routing
  ∧ BelowSensitivitySupportReady c.ledger
  ∧ c.semantics.admission = .admitted
  ∧ c.semantics.applicability = .live
  ∧ c.semantics.rawExecution = .unresolved .belowSensitivity
  ∧ c.semantics.channelRelation = .belowSensitivity

/-! --------------------------------------------------------------------------
25. v0.5 generic firewall theorems
---------------------------------------------------------------------------- -/

theorem successor_lineage_fail_blocks_empirical_discrimination_license
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet)
    (hfail : effectiveStatus routing .successorLineage = .fail) :
    ¬ EmpiricalDiscriminationCaseLicensed routing c := by
  simp [EmpiricalDiscriminationCaseLicensed,
        SuccessorLineageSupportReady,
        hfail]

theorem successor_lineage_fail_blocks_exact_nonidentification_license
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet)
    (hfail : effectiveStatus routing .successorLineage = .fail) :
    ¬ ExactNonIdentificationCaseLicensed routing c := by
  simp [ExactNonIdentificationCaseLicensed,
        SuccessorLineageSupportReady,
        hfail]

theorem successor_lineage_fail_blocks_below_sensitivity_license
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet)
    (hfail : effectiveStatus routing .successorLineage = .fail) :
    ¬ BelowSensitivityCaseLicensed routing c := by
  simp [BelowSensitivityCaseLicensed,
        SuccessorLineageSupportReady,
        hfail]

theorem structural_protection_result_disagreement_blocks_license
    {ChannelSet : Type}
    (routing : CasePacket)
    (c : SuccessorExperimentCase ChannelSet)
    (hfail : effectiveStatus routing .successorBaselineProtection = .fail) :
    ¬ StructuralProtectionCaseLicensed routing c := by
  simp [StructuralProtectionCaseLicensed,
        StructuralProtectionResultAgrees,
        hfail]

theorem open_non_sensitivity_seat_blocks_closed_except
    (l : SuccessorExperimentLedger)
    (b : SuccessorExperimentBurden)
    (hne : b ≠ .sensitivity)
    (hopen : l.seat b = some .open) :
    ¬ ExperimentClosedExcept l .sensitivity := by
  intro hclosed
  have hs := hclosed b hne
  simp [ExperimentSeatClosed, hopen] at hs

theorem open_non_sensitivity_seat_blocks_below_sensitivity_support
    (l : SuccessorExperimentLedger)
    (b : SuccessorExperimentBurden)
    (hne : b ≠ .sensitivity)
    (hopen : l.seat b = some .open) :
    ¬ BelowSensitivitySupportReady l := by
  intro hs
  exact (open_non_sensitivity_seat_blocks_closed_except l b hne hopen) hs.2.1

/-! --------------------------------------------------------------------------
26. Fixture A — epoch-local global sequestering: NOT IDENTIFIABLE
---------------------------------------------------------------------------- -/

def epochLocalSequesteringLedger : SuccessorExperimentLedger where
  route := .epochLocal
  seat := fun b =>
    match b with
    | .realChange => some .discharged
    | .protectedSectorMembership => some .discharged
    | .piRelevantChange => some .discharged
    | .mechanismApplicability => some .discharged
    | .inheritedTheoryData => some .discharged
    | .variationConnection => some .discharged
    | .falsificationConnection => some .discharged
    | .freeDatumStability => some .discharged
    | .completionIdentity => none
    | .forwardModel => some .discharged
    | .channelSet => some .discharged
    | .fittedComparator => some .discharged
    | .mappability => some .discharged
    | .degeneracyTest => some .discharged
    | .resultFreeze => some .discharged
    | _ => none

def epochLocalSequesteringPacket : SemanticPacket Unit where
  channelSet := ()
  admission := .admitted
  applicability := .notIdentifiable
  rawExecution := .notRun
  provenance := {
    structural := false
    computational := false
    empirical := false
  }
  protection := .nonvacuous
  channelRelation := .constraintFixedChannelEquivalent
  evidenceDependence := .partiallyShared

def epochLocalSequesteringCase : SuccessorExperimentCase Unit where
  ledger := epochLocalSequesteringLedger
  semantics := epochLocalSequesteringPacket

theorem epoch_local_sequestering_is_not_empirical_discrimination :
    effectiveExecution epochLocalSequesteringPacket = .notRun
    ∧ ¬ EmpiricalDiscriminationPass epochLocalSequesteringPacket := by
  simp [epochLocalSequesteringPacket,
        effectiveExecution,
        executionAllowed,
        EmpiricalDiscriminationPass]

/-! --------------------------------------------------------------------------
27. Fixture B — original global population: whole-history OPEN
---------------------------------------------------------------------------- -/

def wholeHistorySequesteringLedger : SuccessorExperimentLedger where
  route := .wholeHistory
  seat := fun b =>
    match b with
    | .realChange => some .discharged
    | .protectedSectorMembership => some .discharged
    | .piRelevantChange => some .discharged
    | .mechanismApplicability => some .discharged
    | .inheritedTheoryData => some .discharged
    | .variationConnection => some .discharged
    | .falsificationConnection => some .discharged
    | .freeDatumStability => some .discharged
    | .fittedComparator => some .discharged
    | .completionIdentity => none
    | .completionViability => none
    | .historyClosure => some .open
    | .forwardModel => some .open
    | .channelSet => some .open
    | .matchedUnprotectedComparator => some .open
    | .alternativeCoverage => some .open
    | .mappability => some .open
    | .degeneracyTest => some .open
    | .sensitivity => some .open
    | .dataAdequacy => some .open
    | .dataConsistency => some .open
    | .resultFreeze => some .open

def wholeHistorySequesteringPacket : SemanticPacket Unit where
  channelSet := ()
  admission := .admitted
  applicability := .live
  rawExecution := .unresolved .channelOpen
  provenance := {
    structural := false
    computational := false
    empirical := false
  }
  protection := .nonvacuous
  channelRelation := .channelOpen
  evidenceDependence := .partiallyShared

def wholeHistorySequesteringCase : SuccessorExperimentCase Unit where
  ledger := wholeHistorySequesteringLedger
  semantics := wholeHistorySequesteringPacket

theorem whole_history_history_closure_seat_is_open :
    wholeHistorySequesteringLedger.seat .historyClosure = some .open := by
  rfl

/-- Forward modeling remains an additional open implementation seat. -/
theorem whole_history_forward_model_seat_is_open :
    wholeHistorySequesteringLedger.seat .forwardModel = some .open := by
  rfl

theorem whole_history_current_route_not_ready_for_empirical_run :
    ¬ ExperimentReadyForEmpiricalRun wholeHistorySequesteringLedger := by
  exact open_required_seat_blocks_empirical_readiness
    wholeHistorySequesteringLedger .historyClosure rfl

theorem whole_history_channel_open_blocks_empirical_pass :
    effectiveExecution wholeHistorySequesteringPacket
      = .unresolved .channelOpen
    ∧ ¬ EmpiricalDiscriminationPass wholeHistorySequesteringPacket := by
  simp [wholeHistorySequesteringPacket,
        effectiveExecution,
        executionAllowed,
        EmpiricalDiscriminationPass]

/-! --------------------------------------------------------------------------
28. Fixture C — published negative linear-potential completion
---------------------------------------------------------------------------- -/

/--
Domain-supplied negative fixture. The published scientific adjudication is
represented as a VIOLATED completion-viability seat. Lean does not derive the
physical violation.
-/
def linearPotentialCompletionLedger : SuccessorExperimentLedger where
  route := .wholeHistory
  seat := fun b =>
    match b with
    | .realChange => some .discharged
    | .protectedSectorMembership => some .discharged
    | .piRelevantChange => some .discharged
    | .mechanismApplicability => some .discharged
    | .inheritedTheoryData => some .discharged
    | .variationConnection => some .discharged
    | .falsificationConnection => some .discharged
    | .freeDatumStability => some .discharged
    | .completionIdentity => some .discharged
    | .completionViability => some .violated
    | .resultFreeze => some .discharged
    | _ => none

def linearPotentialCompletionPacket : SemanticPacket Unit where
  channelSet := ()
  admission := .admitted
  applicability := .live
  rawExecution := .fail
  provenance := {
    structural := false
    computational := true
    empirical := false
  }
  protection := .nonvacuous
  channelRelation := .channelOpen
  evidenceDependence := .partiallyShared

def linearPotentialCompletionCase : SuccessorExperimentCase Unit where
  ledger := linearPotentialCompletionLedger
  semantics := linearPotentialCompletionPacket

theorem linear_potential_completion_viability_is_violated :
    linearPotentialCompletionLedger.seat .completionViability
      = some .violated := by
  rfl

theorem linear_potential_completion_not_ready_for_empirical_run :
    ¬ ExperimentReadyForEmpiricalRun linearPotentialCompletionLedger := by
  exact violated_required_seat_blocks_empirical_readiness
    linearPotentialCompletionLedger .completionViability rfl

theorem linear_potential_completion_fails_without_empirical_pass :
    effectiveExecution linearPotentialCompletionPacket = .fail
    ∧ ¬ EmpiricalDiscriminationPass linearPotentialCompletionPacket := by
  simp [linearPotentialCompletionPacket,
        effectiveExecution,
        executionAllowed,
        EmpiricalDiscriminationPass]

/-! --------------------------------------------------------------------------
29. v0.5 fixture routing and firewall checkpoints
---------------------------------------------------------------------------- -/

/-- The epoch-local fixture registers a real successor-lineage claim. -/
def epochLocalSequesteringRouting : CasePacket :=
  continuityOnlyPassPacket

/-- The parent whole-history fixture registers a real successor-lineage claim. -/
def wholeHistorySequesteringRouting : CasePacket :=
  continuityOnlyPassPacket

/-- The completion fixture retains a valid successor lineage despite its completion FAIL. -/
def linearPotentialCompletionRouting : CasePacket :=
  continuityOnlyPassPacket

theorem epoch_local_sequestering_ready_for_registered_support :
    ExperimentReadyForEmpiricalRun epochLocalSequesteringLedger := by
  constructor
  · simp [CoreSuccessorSeatsDeclared, epochLocalSequesteringLedger]
  · intro b
    cases b <;> simp [ExperimentSeatClosed, epochLocalSequesteringLedger]

theorem epoch_local_sequestering_exact_nonidentification_support_ready :
    ExactNonIdentificationSupportReady epochLocalSequesteringLedger := by
  refine ⟨epoch_local_sequestering_ready_for_registered_support, ?_⟩
  simp [epochLocalSequesteringLedger]

theorem epoch_local_sequestering_exact_nonidentification_licensed :
    ExactNonIdentificationCaseLicensed
      epochLocalSequesteringRouting
      epochLocalSequesteringCase := by
  simp [ExactNonIdentificationCaseLicensed,
        SuccessorLineageSupportReady,
        epochLocalSequesteringRouting,
        continuityOnlyPassPacket,
        effectiveStatus,
        live,
        routingUnresolved,
        claimsSuccessorContinuity,
        hasPhysicalSuccessor,
        epoch_local_sequestering_exact_nonidentification_support_ready,
        epochLocalSequesteringCase,
        epochLocalSequesteringPacket]

theorem epoch_local_sequestering_exact_nonidentification_routing_consistent :
    ExactNonIdentificationRoutingConsistent epochLocalSequesteringCase := by
  simp [ExactNonIdentificationRoutingConsistent,
        epochLocalSequesteringCase,
        epochLocalSequesteringPacket,
        epochLocalSequesteringLedger]

theorem epoch_local_sequestering_not_empirical_discrimination_licensed :
    ¬ EmpiricalDiscriminationCaseLicensed
      epochLocalSequesteringRouting
      epochLocalSequesteringCase := by
  intro h
  exact epoch_local_sequestering_is_not_empirical_discrimination.2 h.2.2

theorem whole_history_not_structural_protection_licensed :
    ¬ StructuralProtectionCaseLicensed
      wholeHistorySequesteringRouting
      wholeHistorySequesteringCase := by
  intro h
  exact whole_history_current_route_not_ready_for_empirical_run h.2.2.1.1

theorem whole_history_not_empirical_discrimination_licensed :
    ¬ EmpiricalDiscriminationCaseLicensed
      wholeHistorySequesteringRouting
      wholeHistorySequesteringCase := by
  intro h
  exact whole_history_current_route_not_ready_for_empirical_run h.2.1.1

theorem whole_history_not_exact_nonidentification_licensed :
    ¬ ExactNonIdentificationCaseLicensed
      wholeHistorySequesteringRouting
      wholeHistorySequesteringCase := by
  intro h
  exact whole_history_current_route_not_ready_for_empirical_run h.2.1.1

theorem whole_history_case_is_not_below_sensitivity_licensed :
    ¬ BelowSensitivityCaseLicensed
      wholeHistorySequesteringRouting
      wholeHistorySequesteringCase := by
  intro h
  have hclosed := h.2.1.2.1 .historyClosure (by decide)
  simp [wholeHistorySequesteringCase,
        ExperimentSeatClosed,
        wholeHistorySequesteringLedger] at hclosed

theorem linear_potential_completion_not_structural_protection_licensed :
    ¬ StructuralProtectionCaseLicensed
      linearPotentialCompletionRouting
      linearPotentialCompletionCase := by
  intro h
  exact linear_potential_completion_not_ready_for_empirical_run h.2.2.1.1

theorem linear_potential_completion_not_empirical_discrimination_licensed :
    ¬ EmpiricalDiscriminationCaseLicensed
      linearPotentialCompletionRouting
      linearPotentialCompletionCase := by
  intro h
  exact linear_potential_completion_not_ready_for_empirical_run h.2.1.1

theorem linear_potential_completion_not_exact_nonidentification_licensed :
    ¬ ExactNonIdentificationCaseLicensed
      linearPotentialCompletionRouting
      linearPotentialCompletionCase := by
  intro h
  exact linear_potential_completion_not_ready_for_empirical_run h.2.1.1

/-! --------------------------------------------------------------------------
30. v0.5 experiment-layer machine ceiling
---------------------------------------------------------------------------- -/

/-
A clean elaboration of this v0.5 extension establishes ONLY:

1. The first eight CCP S_m burdens cannot be omitted as `none` in a positively
   ready ledger.
2. Required OPEN or VIOLATED seats block positive experiment readiness.
3. Case-level licenses require an independently closed support surface and a
   domain-supplied terminal scientific adjudication.
4. Successor lineage must itself PASS before an S_m discrimination, exact
   non-identification, below-sensitivity, or structural-protection license can
   carry.
5. Structural-protection terminal representations must agree across the
   top-level routing packet and SemanticPacket.
6. BELOW SENSITIVITY cannot be licensed while another honestly required burden
   remains OPEN; sensitivity itself must be the decisive violated reach seat.
7. Epoch-local exact channel equivalence remains NOT IDENTIFIABLE and is
   machine-licensed only as a conditional claim over its supplied support
   record.
8. The original whole-history population remains OPEN at historyClosure, with
   forwardModel OPEN as an additional burden, and cannot be licensed as BELOW
   SENSITIVITY.
9. The linear-potential completion remains a completion-specific computational
   FAIL and does not acquire a positive S_m case license.
10. No Universal Kernel modification is required.

It does NOT establish the truth of any supplied scientific premise, the physical
adequacy of a comparator, the correctness of an audit outcome, the identity of
records supplied as one real-world case, observational feasibility, data
trustworthiness, empirical support for sequestering, or a numerical-value
selection mechanism. Physics / domain analysis owns those premises and outcomes;
Lean checks the encoded conditional support, license, and routing consequences.
-/

end CosmologicalConstantStabilityRouting
end StructuralFlow
