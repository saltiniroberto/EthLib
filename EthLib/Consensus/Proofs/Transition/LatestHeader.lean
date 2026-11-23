module

public import EthLib.Consensus.Proofs.Transition.BlockRoots
public import EthLib.Consensus.Proofs.Transition.ForkBoundary
public import EthLib.Consensus.Proofs.Transition.Genesis
public import EthLib.Consensus.Proofs.Transition.PayloadInputs
public import EthLib.Consensus.Proofs.Transition.RootLinks
public import EthLib.Consensus.Proofs.Transition.TargetUpgrades

/-!
# Proofs: the latest block header through the steps of a chain

A block leaves its header as the latest block header, at every fork, with a zero state root.

It runs at the slot of the state, after the latest block header, whose root is its parent.

That header has a zero state root until the next slot, which fills it with the root of the state.

A slot step with its upgrades records the root of the latest block header at the slot of the state.

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
  obtain ⟨slot, newer, parentRoot⟩ := processBlock_parentRoot computed
  obtain ⟨bodyRoot, bodyRooted, header⟩ := latestBlockHeader_processBlock computed
  exact ⟨slot, newer, parentRoot, bodyRoot, bodyRooted, header⟩

/-! ## The slots -/

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
    (latestBlockHeader_processUpgrades upgraded).trans header
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
  exact (payloadInputs_processDeposit deposited).latestBlockHeader

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
