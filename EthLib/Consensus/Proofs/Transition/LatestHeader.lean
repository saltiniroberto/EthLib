module

public import EthLib.Consensus.Proofs.Transition.BlockRoots
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Proofs: the latest block header through the steps of a chain

The header step of a block makes the header of the block the latest block header.

That header has a zero state root until the next slot, which fills it with the root of the state.

Every other step of a block keeps the latest block header, at every fork.

So after a block, the latest block header is the header of the block, with a zero state root.

The epoch transition and the upgrades keep the latest block header too.

A slot step records the root of the latest block header at the slot of the state.

Every other root that it records was recorded at the same slot before.

The genesis state built from deposits has a latest block header of slot zero and zero state root.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Uint64 Serialization.Ssz Cryptography.Bls

variable {preset : Preset} {fork : Base.Fork} {config : Config} {checks : SignatureChecks}
  {state after : BeaconState preset fork}

/-- A fold whose every step keeps the latest block header keeps it. -/
theorem latestBlockHeader_foldlM {α ε : Type}
    {step : BeaconState preset fork → α → Except ε (BeaconState preset fork)}
    (kept : ∀ s x s', step s x = .ok s' → s'.latestBlockHeader = s.latestBlockHeader)
    {items : List α} (computed : items.foldlM step state = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader :=
  foldlM_ok_invariant (fun s => s.latestBlockHeader = state.latestBlockHeader)
    (fun _ _ _ before ok => (kept _ _ _ ok).trans before) rfl computed

/-! ## The steps of a block -/

/-- A new validator keeps the latest block header. -/
theorem latestBlockHeader_addValidatorToRegistry {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei}
    (computed : addValidatorToRegistry state pubkey withdrawalCredentials amount = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  unfold addValidatorToRegistry at computed
  split at computed
  · unfold addValidatorToRegistryAltair at computed
    simp only [liftAccessor_ok, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, rfl⟩ := computed
    rfl
  · split at computed
    · cases computed
      rfl
    · cases computed

/-- A deposit credited at once keeps the latest block header. -/
theorem latestBlockHeader_applyPendingDeposit {deposit : PendingDeposit}
    (computed : applyPendingDeposit config checks state deposit = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  unfold applyPendingDeposit at computed
  split at computed
  · split at computed
    · cases computed
      rfl
    simp only [bind, Except.bind] at computed
    split at computed
    · cases computed
    split at computed
    · exact latestBlockHeader_addValidatorToRegistry computed
    · cases computed
      rfl
  · simp only [liftAccessor_ok, bind_ok_iff] at computed
    obtain ⟨_, _, computed⟩ := computed
    exact (payloadInputs_increaseBalance computed).latestBlockHeader

/-- From Electra, a deposit that joins the pending deposits keeps the latest block header. -/
theorem latestBlockHeader_applyDepositElectra {electra : .pectra ≤ fork} {pubkey : BLSPubkey}
    {withdrawalCredentials : Bytes32} {amount : Gwei} {signature : BLSSignature}
    (computed : applyDepositElectra config checks state electra pubkey withdrawalCredentials amount
      signature = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  unfold applyDepositElectra at computed
  split at computed
  · simp only [bind, Except.bind] at computed
    split at computed
    · cases computed
    split at computed
    · split at computed
      · cases computed
      rename_i added
      have kept := latestBlockHeader_addValidatorToRegistry added
      obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
      exact kept
    · cases computed
      rfl
  · obtain ⟨_, rfl⟩ := addPendingDeposit_eq (liftAccessor_ok.mp computed)
    rfl

/-- A deposit keeps the latest block header. -/
theorem latestBlockHeader_processDeposit {before : fork < .hegota} {deposit : Deposit}
    (computed : processDeposit config checks before state deposit = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  obtain ⟨_, _, _, _, applied⟩ := processDeposit_ok computed
  unfold applyDeposit at applied
  split at applied
  · have kept := latestBlockHeader_applyDepositElectra applied
    exact kept
  · have kept := latestBlockHeader_applyPendingDeposit applied
    exact kept

/-- The operations of a block keep the latest block header, at every fork. -/
theorem latestBlockHeader_processOperations {body : BeaconBlockBody preset fork}
    {parentSlot : Slot}
    (computed : processOperations config checks state body parentSlot = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  by_cases gloas : .glamsterdam ≤ fork
  · exact (payloadInputs_processOperations gloas computed).latestBlockHeader
  simp only [processOperations, gloas, ↓reduceDIte, bind_ok_iff, ensure_ok_iff,
    ← Array.foldlM_toList] at computed
  obtain ⟨_, _, _, _, proposed, proposedOk, slashed, slashedOk, attested, attestedOk,
    deposited, depositedOk, exited, exitedOk, changed, changedOk, requested⟩ := computed
  have early := (latestBlockHeader_foldlM (fun _ _ _ ok =>
      (payloadInputs_processVoluntaryExit ok).latestBlockHeader) exitedOk).trans <|
    (latestBlockHeader_foldlM (fun _ _ _ ok => latestBlockHeader_processDeposit ok)
      depositedOk).trans <|
    (latestBlockHeader_foldlM (fun _ _ _ ok =>
      (payloadInputs_processAttestation ok).latestBlockHeader) attestedOk).trans <|
    (latestBlockHeader_foldlM (fun _ _ _ ok =>
      (payloadInputs_processAttesterSlashing ok).latestBlockHeader) slashedOk).trans
    (latestBlockHeader_foldlM (fun _ _ _ ok =>
      (payloadInputs_processProposerSlashing ok).latestBlockHeader) proposedOk)
  -- From Capella the changes of credentials run, and from Electra the requests.
  have changes : changed.latestBlockHeader = exited.latestBlockHeader := by
    unfold processBlsToExecutionChanges at changedOk
    split at changedOk
    · rw [← Array.foldlM_toList] at changedOk
      exact latestBlockHeader_foldlM (fun _ _ _ ok =>
        (payloadInputs_processBlsToExecutionChange ok).latestBlockHeader) changedOk
    · cases changedOk
      rfl
  refine Eq.trans ?_ (changes.trans early)
  split at requested
  · simp only [processExecutionRequests, bind_ok_iff, ← Array.foldlM_toList] at requested
    obtain ⟨_, depositsOk, _, withdrawalsOk, consolidationsOk⟩ := requested
    exact (latestBlockHeader_foldlM (fun _ _ _ ok =>
        (payloadInputs_processConsolidationRequest ok).latestBlockHeader) consolidationsOk).trans <|
      (latestBlockHeader_foldlM (fun _ _ _ ok =>
        (payloadInputs_processWithdrawalRequest ok).latestBlockHeader) withdrawalsOk).trans
      (latestBlockHeader_foldlM (fun _ _ _ ok =>
        (payloadInputs_processDepositRequest ok).latestBlockHeader) depositsOk)
  · simp only [pure, Except.pure, Except.ok.injEq] at requested
    rw [requested]

/-- From Bellatrix, the execution part of a block keeps the latest block header. -/
theorem latestBlockHeader_processBlockExecution {engine : ExecutionEngine preset fork}
    {body : BeaconBlockBody preset fork} {bellatrix : .bellatrix ≤ fork}
    (computed : processBlockExecution config checks engine state body bellatrix = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  unfold processBlockExecution at computed
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, bid⟩ := computed
    exact (payloadInputs_processExecutionPayloadBid bid).latestBlockHeader.trans
      (payloadInputs_processWithdrawals withdrawnOk).latestBlockHeader
  split at computed
  · simp only [bind_ok_iff] at computed
    obtain ⟨_, withdrawnOk, paid⟩ := computed
    obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok paid
    exact (payloadInputs_processWithdrawals withdrawnOk).latestBlockHeader
  · dsimp only at computed
    split at computed
    · obtain ⟨_, _, _, rfl⟩ := processExecutionPayload_ok computed
      rfl
    · cases computed
      rfl

/-- A block leaves its header as the latest block header, at every fork.

The block is at the slot of the state, after the latest block header, whose root is its parent.

The header holds the slot, the proposer and the parent root of the block, and the root of its body.

Its state root is zero. -/
theorem processBlock_latestBlockHeader {engine : ExecutionEngine preset fork}
    {block : BeaconBlock preset fork}
    (computed : processBlock config checks engine state block = .ok after) :
    block.slot = state.slot ∧ state.latestBlockHeader.slot < block.slot ∧
      SszType.hashTreeRoot state.latestBlockHeader = .ok block.parentRoot ∧
      ∃ bodyRoot, SszType.hashTreeRoot block.body = .ok bodyRoot ∧
        after.latestBlockHeader =
          { slot := block.slot, proposerIndex := block.proposerIndex,
            parentRoot := block.parentRoot, stateRoot := Vector.replicate 32 0, bodyRoot } := by
  unfold processBlock at computed
  split at computed
  · unfold processBlockAltair at computed
    simp only [bind_ok_iff] at computed
    obtain ⟨paid, paidOk, headed, headedOk, executed, executedOk, revealed, revealedOk, voted,
      votedOk, operated, operatedOk, synced⟩ := computed
    -- From Gloas the payload of the parent runs first, and keeps the slot and the header.
    have parent : paid.slot = state.slot ∧ paid.latestBlockHeader = state.latestBlockHeader := by
      split at paidOk
      · have inputs := payloadInputs_processParentExecutionPayload paidOk
        exact ⟨inputs.slot, inputs.latestBlockHeader⟩
      · cases paidOk
        exact ⟨rfl, rfl⟩
    have executedKept : executed.latestBlockHeader = headed.latestBlockHeader := by
      split at executedOk
      · exact latestBlockHeader_processBlockExecution executedOk
      · cases executedOk
        rfl
    have votedKept : voted.latestBlockHeader = revealed.latestBlockHeader := by
      split at votedOk
      · exact (payloadInputs_processEth1Data votedOk).latestBlockHeader
      · cases votedOk
        rfl
    obtain ⟨slot, newer, -, parentRoot, -⟩ := processBlockHeader_checks headedOk
    rw [parent.1] at slot
    rw [parent.2] at newer parentRoot
    obtain ⟨bodyRoot, bodyRooted, rfl⟩ := processBlockHeader_eq headedOk
    refine ⟨slot, newer, parentRoot, bodyRoot, bodyRooted, ?_⟩
    exact (payloadInputs_processSyncAggregate synced).latestBlockHeader.trans <|
      (latestBlockHeader_processOperations operatedOk).trans <|
      votedKept.trans <| (payloadInputs_processRandao revealedOk).latestBlockHeader.trans
        executedKept
  · simp only [bind_ok_iff] at computed
    obtain ⟨headed, headedOk, revealed, revealedOk, voted, votedOk, operatedOk⟩ := computed
    obtain ⟨slot, newer, -, parentRoot, -⟩ := processBlockHeader_checks headedOk
    obtain ⟨bodyRoot, bodyRooted, rfl⟩ := processBlockHeader_eq headedOk
    refine ⟨slot, newer, parentRoot, bodyRoot, bodyRooted, ?_⟩
    exact (latestBlockHeader_processOperations operatedOk).trans <|
      (payloadInputs_processEth1Data votedOk).latestBlockHeader.trans
        (payloadInputs_processRandao revealedOk).latestBlockHeader

/-! ## The upgrades -/

/-- Queueing a validator that is not yet active keeps the latest block header. -/
private theorem latestBlockHeader_queuePreActivation {electra : .pectra ≤ fork}
    {index : ValidatorIndex} (computed : queuePreActivation state electra index = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  simp only [queuePreActivation, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
    Except.ok.injEq] at computed
  obtain ⟨_, -, _, -, _, -, _, set₁, _, set₂, rfl⟩ := computed
  obtain ⟨_, rfl⟩ := setBalance_ok set₁
  obtain ⟨_, rfl⟩ := setValidator_ok set₂
  rfl

/-- Queueing the excess balance of a validator keeps the latest block header. -/
private theorem latestBlockHeader_queueCompoundingExcess {electra : .pectra ≤ fork} {index : Nat}
    (computed : queueCompoundingExcess state electra index = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  unfold queueCompoundingExcess at computed
  split at computed
  · split at computed
    · have queued := liftAccessor_ok.mp computed
      simp only [queueExcessActiveBalance, bind_ok_iff] at queued
      obtain ⟨_, _, queued⟩ := queued
      split at queued
      · simp only [bind_ok_iff, pure, Except.pure, Except.ok.injEq] at queued
        obtain ⟨_, _, _, _, _, set, rfl⟩ := queued
        obtain ⟨_, rfl⟩ := setBalance_ok set
        rfl
      · cases queued
        rfl
    · cases computed
      rfl
  · cases computed
    rfl

/-- Each upgrade keeps the latest block header. -/
theorem upgradeNext_latestBlockHeader {pre : ForkedBeaconState preset}
    {post : {post : ForkedBeaconState preset // pre.fork < post.fork}}
    (computed : upgradeNext config checks pre = .ok post) :
    post.val.state.latestBlockHeader = pre.state.latestBlockHeader := by
  obtain ⟨fork, state⟩ := pre
  cases fork
  case phase0 =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨_, folded, _, rfl⟩ := upgradeToAltair_ok upgraded
    obtain ⟨_, rfl, -⟩ := foldlM_translateAttestation folded
    rfl
  case altair | bellatrix | shapella =>
    simp only [upgradeNext, pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl
  case dencun =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToElectra, bind_ok_iff] at upgraded
    obtain ⟨_, -, _, -, _, -, _, -, _, queued, compounded⟩ := upgraded
    exact (latestBlockHeader_foldlM (fun _ _ _ ok => latestBlockHeader_queueCompoundingExcess ok)
      compounded).trans
      (latestBlockHeader_foldlM (fun _ _ _ ok => latestBlockHeader_queuePreActivation ok) queued)
  case pectra =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToFulu, bind_ok_iff, liftAccessor_ok, pure, Except.pure,
      Except.ok.injEq] at upgraded
    obtain ⟨_, _, rfl⟩ := upgraded
    rfl
  case fusaka =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    simp only [upgradeToGloas, bind_ok_iff, liftSsz_ok, liftAccessor_ok] at upgraded
    obtain ⟨_, _, _, _, onboarded⟩ := upgraded
    obtain ⟨⟨_, _, rfl⟩, -⟩ := onboardBuildersFromPendingDeposits_spec onboarded
    rfl
  case glamsterdam =>
    simp only [upgradeNext, bind_ok_iff, pure, Except.pure, Except.ok.injEq] at computed
    obtain ⟨_, upgraded, rfl⟩ := computed
    obtain ⟨-, rfl⟩ := upgradeToHeze_ok_iff.mp upgraded
    rfl
  all_goals
    simp only [upgradeNext] at computed
    cases computed

/-- The upgrades due at a slot keep the latest block header. -/
theorem processUpgrades_latestBlockHeader {forked after : ForkedBeaconState preset}
    (computed : processUpgrades config checks forked = .ok after) :
    after.state.latestBlockHeader = forked.state.latestBlockHeader :=
  processUpgrades_induction
    (property := fun state => state.state.latestBlockHeader = forked.state.latestBlockHeader)
    (fun same stepOk => (upgradeNext_latestBlockHeader stepOk).trans same) rfl computed

/-! ## The slots -/

/-- The caching of a slot fills the state root of the latest block header, if it is zero.

It fills it with the root of the state before the caching. -/
theorem processSlot_latestBlockHeader (computed : processSlot state = .ok after) :
    ∃ stateRoot, SszType.hashTreeRoot state = .ok stateRoot ∧
      after.latestBlockHeader =
        if state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
          { state.latestBlockHeader with stateRoot }
        else state.latestBlockHeader := by
  unfold processSlot at computed
  simp only [bind_ok_iff, liftSsz_ok, liftAccessor_ok] at computed
  obtain ⟨stateRoot, hashed, _, _, _, _, _, _, computed⟩ := computed
  refine ⟨stateRoot, hashed, ?_⟩
  split at computed
  · obtain ⟨_, _, _, _, rfl⟩ := unsetNextPayloadAvailability_ok (liftAccessor_ok.mp computed)
    rfl
  · simp only [pure, Except.pure, Except.ok.injEq] at computed
    subst computed
    rfl

/-- One slot step with its upgrades: the header it leaves latest, and the roots it records.

The caching fills the state root of the latest block header when it is zero, with the state root.

That header is the latest block header after the step, one slot later.

The step records the root of that header at the slot of the state before it.

Every other root that it records was recorded at the same slot before. -/
theorem advanceSlotAcross_latestBlockHeader {forked after : ForkedBeaconState preset}
    (computed : advanceSlotAcross config checks forked = .ok after) :
    (∃ stateRoot, SszType.hashTreeRoot forked.state = .ok stateRoot ∧
      after.state.latestBlockHeader =
        if forked.state.latestBlockHeader.stateRoot = Vector.replicate 32 0 then
          { forked.state.latestBlockHeader with stateRoot }
        else forked.state.latestBlockHeader) ∧
      after.state.slot.toNat = forked.state.slot.toNat + 1 ∧
      ∀ (slot : Slot) (root : Root), getBlockRootAtSlot after.state slot = .ok root →
        (slot = forked.state.slot ∧
            SszType.hashTreeRoot after.state.latestBlockHeader = .ok root) ∨
          (slot.toNat < forked.state.slot.toNat ∧
            getBlockRootAtSlot forked.state slot = .ok root) := by
  obtain ⟨advanced, advancedOk, upgraded⟩ := bind_ok_iff.mp computed
  obtain ⟨cached, cachedOk, -, roots, header, -, -, sum⟩ := advanceSlot_cachedRoots advancedOk
  have slotKept := processUpgrades_slot upgraded
  have rootsKept := processUpgrades_blockRoots upgraded
  have headerKept : after.state.latestBlockHeader = cached.latestBlockHeader :=
    (processUpgrades_latestBlockHeader upgraded).trans header
  obtain ⟨stateRoot, hashed, filled⟩ := processSlot_latestBlockHeader cachedOk
  obtain ⟨written, writtenRoot, write⟩ := processSlot_blockRoots cachedOk
  have later : after.state.slot.toNat = forked.state.slot.toNat + 1 := by
    rw [slotKept]
    exact sum
  refine ⟨⟨stateRoot, hashed, headerKept.trans filled⟩, later, fun slot root read => ?_⟩
  obtain ⟨lt, fits, within, readOk⟩ := getBlockRootAtSlot_ok_iff.mp read
  rw [rootsKept] at readOk
  change readCircular advanced.blockRoots.elements slot = .ok root at readOk
  rw [roots] at readOk
  by_cases same : slot = forked.state.slot
  · refine .inl ⟨same, ?_⟩
    rw [same, readCircular_writeCircular write] at readOk
    rw [headerKept, writtenRoot, Except.ok.inj readOk]
  · have older : slot.toNat < forked.state.slot.toNat := by
      have different : slot.toNat ≠ forked.state.slot.toNat := fun equal =>
        same (UInt64.toNat_inj.mp equal)
      omega
    refine .inr ⟨older, getBlockRootAtSlot_ok_iff.mpr ⟨older, fits, by omega, ?_⟩⟩
    have other : forked.state.slot % preset.SLOTS_PER_HISTORICAL_ROOT ≠
        slot % preset.SLOTS_PER_HISTORICAL_ROOT := by
      intro equal
      have equal' := congrArg UInt64.toNat equal
      rw [UInt64.toNat_mod, UInt64.toNat_mod] at equal'
      exact Nat.mod_ne_of_sub_lt older (by omega) equal'
    rw [readCircular_writeCircular_of_ne write other] at readOk
    exact readOk

/-! ## Genesis -/

/-- A deposit at genesis keeps the latest block header. -/
private theorem latestBlockHeader_genesisDeposit {before : fork < .hegota}
    {leaves : Array DepositData} {entry : Deposit × Nat}
    (computed : genesisDeposit config checks before leaves state entry = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  simp only [genesisDeposit, bind_ok_iff] at computed
  obtain ⟨_, _, deposited⟩ := computed
  have kept := latestBlockHeader_processDeposit deposited
  exact kept

/-- An activation at genesis keeps the latest block header. -/
private theorem latestBlockHeader_activateAtGenesis {index : Nat}
    (computed : activateAtGenesis state index = .ok after) :
    after.latestBlockHeader = state.latestBlockHeader := by
  simp only [activateAtGenesis, bind_ok_iff, liftAccessor_ok] at computed
  obtain ⟨_, _, _, _, set⟩ := computed
  exact (payloadInputs_setValidatorAt set).latestBlockHeader

/-- The genesis state built from deposits has a latest block header of slot zero.

Its state root is zero. -/
theorem initializeBeaconStateFromEth1_latestBlockHeader {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    (computed : initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits =
      .ok after) :
    after.latestBlockHeader.slot = 0 ∧
      after.latestBlockHeader.stateRoot = Vector.replicate 32 0 := by
  obtain ⟨_, _, _, _, activated, _, depositedOk, activatedOk, rfl⟩ :=
    initializeBeaconStateFromEth1_ok computed
  have deposited :=
    latestBlockHeader_foldlM (fun _ _ _ ok => latestBlockHeader_genesisDeposit ok) depositedOk
  have kept :=
    latestBlockHeader_foldlM (fun _ _ _ ok => latestBlockHeader_activateAtGenesis ok) activatedOk
  have header := kept.trans deposited
  refine ⟨?_, ?_⟩
  · change activated.latestBlockHeader.slot = 0
    rw [header]
    rfl
  · change activated.latestBlockHeader.stateRoot = Vector.replicate 32 0
    rw [header]
    rfl

end EthLib.Consensus
