module

public import EthLib.Consensus.Proofs.Containers.Block
public import EthLib.Consensus.Proofs.Transition.FfgTwoChainLists
public import EthLib.Consensus.Proofs.Transition.LatestHeader

/-!
# Proofs: accountable safety for two chains given as lists, with the hash events named

Two chains given as data start from one genesis state, and each finalizes a listed block.

The two finalized blocks conflict: neither chain applies one of them at or before the other.

Then validators are slashable, or the hashes failed in one of two named ways.

The first way is a collision among the headers that the two chains record.

The second way is the zero root, the specification's value for no block and for no state root.
-/

@[expose] public section

namespace EthLib.Consensus

open Base Models Models.Ffg Serialization Serialization.Ssz

variable {preset : Preset} {config : Config} {checks : SignatureChecks}

/-- A chain applies the block `older` at or before the block `newer`, blocks compared as messages.
-/
def ChainList.AppliesAtOrBefore {first last : ForkedBeaconState preset}
    (chain : ChainList config checks first last)
    (older newer : (fork : Fork) × BeaconBlock preset fork) : Prop :=
  ∃ i j : Nat, i ≤ j ∧ chain.blocks[i]? = some older ∧ chain.blocks[j]? = some newer

/-- The last state of a chain is one of its states. -/
theorem ChainList.last_mem_states {first : ForkedBeaconState preset} :
    ∀ {last : ForkedBeaconState preset}, (chain : ChainList config checks first last) →
      last ∈ chain.states
  | _, .nil => List.mem_singleton_self _
  | _, .slot _ _ => List.mem_append_right _ (List.mem_singleton_self _)
  | _, .block _ _ _ _ _ => List.mem_append_right _ (List.mem_singleton_self _)

/-- Each block that a chain applies comes after slot zero.

Its slot is after the slot of the latest block header of the state that it runs on. -/
theorem ChainList.slot_ne_zero_of_mem_blocks {first last : ForkedBeaconState preset}
    (chain : ChainList config checks first last)
    {block : (fork : Fork) × BeaconBlock preset fork} (member : block ∈ chain.blocks) :
    block.2.slot ≠ 0 := by
  obtain ⟨applied, appliedMember, rfl⟩ := List.mem_map.mp member
  obtain ⟨-, _, _, computed⟩ := chain.mem_appliedBlocks appliedMember
  obtain ⟨-, newer, -⟩ := processBlock_latestBlockHeader (applySignedBlock_ok computed).2.1
  intro zero
  rw [zero] at newer
  exact UInt64.not_lt_zero newer

/-- The blocks of a chain that ends with a block step are those before it, then that block. -/
private theorem ChainList.blocks_block {first : ForkedBeaconState preset} {fork : Fork}
    {state after : BeaconState preset fork} (earlier : ChainList config checks first ⟨fork, state⟩)
    (engine : ExecutionEngine preset fork) (signed : SignedBeaconBlock preset fork)
    (validateResult : Bool)
    (applied : applySignedBlock config checks engine state signed validateResult = .ok after) :
    (ChainList.block earlier engine signed validateResult applied).blocks =
      earlier.blocks ++ [⟨fork, signed.message⟩] := by
  simp [ChainList.blocks, ChainList.appliedBlocks]

/-- A header keeps its state root when that root is first set to zero and then set back. -/
private theorem header_stateRoot_restored (header : BeaconBlockHeader) :
    { { header with stateRoot := Vector.replicate 32 0 } with stateRoot := header.stateRoot } =
      header :=
  rfl

/-- An entry of a list is an entry of the list with more entries after it. -/
private theorem getElem?_append_of_eq_some {α : Type} {list : List α} {i : Nat} {entry : α}
    (extra : List α) (found : list[i]? = some entry) : (list ++ extra)[i]? = some entry := by
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp found).1]
  exact found

/-- A chain from the genesis state that applies a block passes through a step from that state.

The first step of such a chain is a slot, which computes the root of the genesis state.

A block cannot come first, as the genesis state is at the slot of its latest block header. -/
private theorem ChainList.genesisRooted {fork : Fork} {state : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok state) :
    ∀ {last : ForkedBeaconState preset} (chain : ChainList config checks ⟨fork, state⟩ last),
      (last = ⟨fork, state⟩ ∧ chain.blocks = []) ∨ ∃ root, SszType.hashTreeRoot state = .ok root
  | _, .nil => .inl ⟨rfl, rfl⟩
  | _, .slot earlier advanced => by
    rcases ChainList.genesisRooted computed earlier with ⟨rfl, -⟩ | rooted
    · obtain ⟨⟨root, rooted, -⟩, -, -⟩ := advanceSlotAcross_latestBlockHeader advanced
      exact .inr ⟨root, rooted⟩
    · exact .inr rooted
  | _, .block earlier _ _ _ applied => by
    rcases ChainList.genesisRooted computed earlier with ⟨same, -⟩ | rooted
    · obtain ⟨slotEq, newer, -⟩ := processBlock_latestBlockHeader (applySignedBlock_ok applied).2.1
      have stateSlot := congrArg (fun forked : ForkedBeaconState preset => forked.state.slot) same
      have headerSlot := congrArg
        (fun forked : ForkedBeaconState preset => forked.state.latestBlockHeader.slot) same
      dsimp only at stateSlot headerSlot
      rw [headerSlot, slotEq, stateSlot,
        (initializeBeaconStateFromEth1_latestBlockHeader computed).1,
        (initializeBeaconStateFromEth1_checkpoints computed).1] at newer
      exact absurd newer (UInt64.lt_irrefl _)
    · exact .inr rooted

/-! ## The headers that a chain records -/

/-- The headers that a list of blocks records after a genesis header, in order.

The first header is the genesis header, and the one after the position of a block is its header.

The root of the header of a block is the root of the block.

The root of the header before a block is the parent root of the block. -/
private structure RecordedHeaders (genesis : BeaconBlockHeader)
    (blocks : List ((fork : Fork) × BeaconBlock preset fork)) (headers : List BeaconBlockHeader) :
    Prop where
  length : headers.length = blocks.length + 1
  first : headers[0]? = some genesis
  listed : ∀ (i : Nat) (block : (fork : Fork) × BeaconBlock preset fork), blocks[i]? = some block →
    ∃ parent header, headers[i]? = some parent ∧ headers[i + 1]? = some header ∧
      SszType.hashTreeRoot parent = .ok block.2.parentRoot ∧
      SszType.hashTreeRoot header = SszType.hashTreeRoot block.2

/-- The header after the position of a block has the root of that block. -/
private theorem RecordedHeaders.block_of_succ {genesis : BeaconBlockHeader}
    {blocks : List ((fork : Fork) × BeaconBlock preset fork)} {headers : List BeaconBlockHeader}
    (recorded : RecordedHeaders genesis blocks headers) {i : Nat} {header : BeaconBlockHeader}
    (found : headers[i + 1]? = some header) :
    ∃ block, blocks[i]? = some block ∧
      SszType.hashTreeRoot header = SszType.hashTreeRoot block.2 := by
  have within := (List.getElem?_eq_some_iff.mp found).1
  have inside : i < blocks.length := by
    have := recorded.length
    omega
  obtain ⟨_, next, -, nextFound, -, nextRoot⟩ :=
    recorded.listed i blocks[i] (List.getElem?_eq_getElem inside)
  rw [found] at nextFound
  cases nextFound
  exact ⟨blocks[i], List.getElem?_eq_getElem inside, nextRoot⟩

/-- A link that a state records, read along a list of headers.

It is a root and itself, the roots of two consecutive headers, or the zero root and the first.
-/
private def LinkAlong (headers : List BeaconBlockHeader) (link : Root × Root) : Prop :=
  link.1 = link.2 ∨
    (∃ i parent header, headers[i]? = some parent ∧ headers[i + 1]? = some header ∧
      SszType.hashTreeRoot parent = .ok link.1 ∧ SszType.hashTreeRoot header = .ok link.2) ∨
    (link.1 = Vector.replicate 32 0 ∧ ∃ first, headers[0]? = some first ∧
      SszType.hashTreeRoot first = .ok link.2)

/-- A link along a list of headers is a link along the list with more headers after it. -/
private theorem LinkAlong.append {headers : List BeaconBlockHeader} {link : Root × Root}
    (extra : List BeaconBlockHeader) (along : LinkAlong headers link) :
    LinkAlong (headers ++ extra) link := by
  rcases along with same | ⟨i, parent, header, parentFound, found, parentRoot, root⟩ |
    ⟨zero, first, firstFound, root⟩
  · exact .inl same
  · exact .inr (.inl ⟨i, parent, header, getElem?_append_of_eq_some extra parentFound,
      getElem?_append_of_eq_some extra found, parentRoot, root⟩)
  · exact .inr (.inr ⟨zero, first, getElem?_append_of_eq_some extra firstFound, root⟩)

/-- The header at a position of a list is the latest one of a state, and what the state records.

Either the state holds it as its latest block header, and recorded its root at the slot before.

Or the state holds it with a zero state root, and has its state root as its own root. -/
private def TipOf (headers : List BeaconBlockHeader) (count : Nat) {fork : Fork}
    (state : BeaconState preset fork) : Prop :=
  -- The header's state root is not zero, and a state at slot zero is at the first position.
  ∃ tip, headers[count]? = some tip ∧ tip.stateRoot ≠ Vector.replicate 32 0 ∧
    (state.slot = 0 → count = 0) ∧
    ((state.latestBlockHeader = tip ∧
        ∀ root, getBlockRootAtSlot state (state.slot - 1) = .ok root →
          SszType.hashTreeRoot tip = .ok root) ∨
      (state.latestBlockHeader = { tip with stateRoot := Vector.replicate 32 0 } ∧
        -- The header is then at the slot of the state.
        SszType.hashTreeRoot state = .ok tip.stateRoot ∧ tip.slot = state.slot ∧
        -- The root recorded at the slot before is then the root of the header before it.
        ∀ root, getBlockRootAtSlot state (state.slot - 1) = .ok root →
          ∃ before prior, before + 1 = count ∧ headers[before]? = some prior ∧
            SszType.hashTreeRoot prior = .ok root))

/-- A slot step keeps the header at a position latest, and records links along the headers.

The state before the step must have that header as its tip, and its links along the headers.

The state after the step has the header as its tip, and its links along the headers. -/
private theorem TipOf.advanceSlotAcross {headers : List BeaconBlockHeader} {count : Nat}
    {forked after : ForkedBeaconState preset} (tipOf : TipOf headers count forked.state)
    (links : ∀ link ∈ rootLinks forked.state, LinkAlong headers link)
    (advanced : advanceSlotAcross config checks forked = .ok after) :
    TipOf headers count after.state ∧ ∀ link ∈ rootLinks after.state, LinkAlong headers link := by
  obtain ⟨tip, tipFound, tipNonzero, slotZero, tipCases⟩ := tipOf
  obtain ⟨⟨stateRoot, hashed, filled⟩, later, reads⟩ := advanceSlotAcross_latestBlockHeader advanced
  -- The caching leaves the tip as the latest block header.
  have headerTip : after.state.latestBlockHeader = tip := by
    rw [filled]
    rcases tipCases with ⟨settled, -⟩ | ⟨fresh, hashedTip, -, -⟩
    · rw [settled, ite_eq_right tipNonzero]
    · rw [hashed] at hashedTip
      cases hashedTip
      rw [fresh, ite_eq_left rfl]
  have bound := UInt64.toNat_lt after.state.slot
  have previous : after.state.slot - 1 = forked.state.slot := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_sub_of_le _ _ (UInt64.le_iff_toNat_le.mpr (by simp; omega)), later]
    simp
  refine ⟨⟨tip, tipFound, tipNonzero, fun zero => ?_, .inl ⟨headerTip, fun root read => ?_⟩⟩,
    fun link linked => ?_⟩
  · rw [zero] at later
    simp at later
  · rw [previous] at read
    rcases reads _ _ read with ⟨-, root⟩ | ⟨older, -⟩
    · rwa [headerTip] at root
    · omega
  simp only [rootLinks, Set.mem_ofPred_eq] at linked
  rcases linked with ⟨slot, first, second⟩ | ⟨zero, first⟩
  · have firstBound := (getBlockRootAtSlot_ok_iff.mp first).1
    have succ : (slot + 1).toNat = slot.toNat + 1 := by
      rw [UInt64.toNat_add, UInt64.toNat_one, Nat.mod_eq_of_lt (by omega)]
    rcases reads _ _ first with ⟨same, -⟩ | ⟨older, firstOld⟩
    · rcases reads _ _ second with ⟨same', -⟩ | ⟨older', -⟩
      · have := congrArg UInt64.toNat same'
        rw [succ, ← same] at this
        omega
      · rw [succ, ← same] at older'
        omega
    rcases reads _ _ second with ⟨same', secondRoot⟩ | ⟨older', secondOld⟩
    · -- The link ends at the slot of the state before: the tip, after itself or the one before.
      rw [headerTip] at secondRoot
      have before : forked.state.slot - 1 = slot := by
        rw [← same']
        simp
      rcases tipCases with ⟨-, settledRead⟩ | ⟨-, -, -, freshRead⟩
      · have firstRoot := settledRead link.1 (by rw [before]; exact firstOld)
        rw [firstRoot] at secondRoot
        exact .inl (Except.ok.inj secondRoot)
      · obtain ⟨index, prior, sum, priorFound, priorRoot⟩ :=
          freshRead link.1 (by rw [before]; exact firstOld)
        refine .inr (.inl ⟨index, prior, tip, priorFound, ?_, priorRoot, secondRoot⟩)
        rw [sum]
        exact tipFound
    · exact links _ (.inl ⟨slot, firstOld, secondOld⟩)
  · rcases reads _ _ first with ⟨same, root⟩ | ⟨-, old⟩
    · have counted := slotZero same.symm
      subst counted
      rw [headerTip] at root
      exact .inr (.inr ⟨zero, tip, tipFound, root⟩)
    · exact links _ (.inr ⟨zero, old⟩)

/-- The headers that a chain from the genesis state records, and what each of its states records.

The genesis state must have a nonzero root, and each listed block its true nonzero state root.

Each link that a state of the chain records is a link along these headers.

The last state has the header of its last block, or the genesis header, as its tip. -/
private theorem ChainList.recordedHeaders {fork : Fork} {state : BeaconState preset fork}
    {eth1BlockHash : Hash32} {eth1Timestamp : UInt64} {deposits : Array Deposit}
    {before : fork < .altair}
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok state)
    {genesisRoot : Root} (rooted : SszType.hashTreeRoot state = .ok genesisRoot)
    (nonzero : genesisRoot ≠ Vector.replicate 32 0) :
    ∀ {last : ForkedBeaconState preset} (chain : ChainList config checks ⟨fork, state⟩ last),
      (∀ applied ∈ chain.appliedBlocks,
        SszType.hashTreeRoot applied.after = .ok applied.signed.message.stateRoot) →
      (∀ applied ∈ chain.appliedBlocks,
        SszType.hashTreeRoot applied.after ≠ .ok (Vector.replicate 32 0)) →
      -- The headers are the genesis header, then the header of each listed block.
      ∃ headers, RecordedHeaders { state.latestBlockHeader with stateRoot := genesisRoot }
          chain.blocks headers ∧
        (∀ forked ∈ chain.states, ∀ link ∈ rootLinks forked.state, LinkAlong headers link) ∧
        TipOf headers chain.blocks.length last.state
  | _, .nil, _, _ => by
    obtain ⟨headerSlot, headerRoot⟩ := initializeBeaconStateFromEth1_latestBlockHeader computed
    have stateSlot := (initializeBeaconStateFromEth1_checkpoints computed).1
    have unread : ∀ slot root, getBlockRootAtSlot state slot ≠ .ok root :=
      getBlockRootAtSlot_initializeBeaconStateFromEth1 computed
    refine ⟨[{ state.latestBlockHeader with stateRoot := genesisRoot }],
      ⟨rfl, rfl, fun i block found => ?_⟩, fun forked member link linked => ?_, ?_⟩
    · simp [ChainList.blocks, ChainList.appliedBlocks] at found
    · simp only [ChainList.states, List.mem_singleton] at member
      subst member
      simp only [rootLinks, Set.mem_ofPred_eq] at linked
      rcases linked with ⟨slot, read, -⟩ | ⟨-, read⟩
      · exact absurd read (unread _ _)
      · exact absurd read (unread _ _)
    · refine ⟨_, rfl, nonzero, fun _ => rfl, .inr ⟨?_, rooted, ?_,
        fun root read => absurd read (unread _ _)⟩⟩
      · change state.latestBlockHeader =
          { state.latestBlockHeader with stateRoot := Vector.replicate 32 0 }
        rw [← headerRoot]
      · change state.latestBlockHeader.slot = state.slot
        rw [headerSlot, stateSlot]
        rfl
  | _, .slot (forked := forked) earlier advanced, stateRooted, nonzeroAfter => by
    obtain ⟨headers, recorded, links, tipOf⟩ := ChainList.recordedHeaders computed rooted nonzero
      earlier stateRooted nonzeroAfter
    obtain ⟨tipOf', links'⟩ :=
      tipOf.advanceSlotAcross (links _ earlier.last_mem_states) advanced
    refine ⟨headers, recorded, fun member found link linked => ?_, tipOf'⟩
    rcases List.mem_append.mp found with old | new
    · exact links _ old link linked
    · obtain rfl := List.mem_singleton.mp new
      exact links' link linked
  | _, .block (fork := blockFork) (state := before) (after := after) earlier engine signed
      validateResult applied, stateRooted, nonzeroAfter => by
    have appliedMember : (⟨blockFork, before, signed, after⟩ : AppliedBlock preset) ∈
        (ChainList.block earlier engine signed validateResult applied).appliedBlocks :=
      List.mem_append_right _ (List.mem_singleton_self _)
    obtain ⟨headers, recorded, links, tip, tipFound, tipNonzero, -, tipCases⟩ :=
      ChainList.recordedHeaders computed rooted nonzero earlier
        (fun applied member => stateRooted applied (List.mem_append_left _ member))
        (fun applied member => nonzeroAfter applied (List.mem_append_left _ member))
    have afterRooted := stateRooted _ appliedMember
    have afterNonzero := nonzeroAfter _ appliedMember
    have blockOk := (applySignedBlock_ok applied).2.1
    obtain ⟨slotEq, newer, parentRooted, bodyRoot, bodyRooted, headerEq⟩ :=
      processBlock_latestBlockHeader blockOk
    have frameSlot := (frame_processBlock blockOk).slot
    have roots := processBlock_blockRoots blockOk
    -- The block runs on a state whose latest block header has its state root.
    obtain ⟨settled, settledRead⟩ : before.latestBlockHeader = tip ∧
        ∀ root, getBlockRootAtSlot before (before.slot - 1) = .ok root →
          SszType.hashTreeRoot tip = .ok root := by
      rcases tipCases with settled | ⟨fresh, -, tipSlot, -⟩
      · exact settled
      · rw [fresh] at newer
        change tip.slot < signed.message.slot at newer
        rw [tipSlot, slotEq] at newer
        exact absurd newer (UInt64.lt_irrefl _)
    have sameLinks : rootLinks after = rootLinks before := by
      simp only [rootLinks, getBlockRootAtSlot_congr frameSlot roots]
    have lengthEq := recorded.length
    let header : BeaconBlockHeader :=
      ⟨signed.message.slot, signed.message.proposerIndex, signed.message.parentRoot,
        signed.message.stateRoot, bodyRoot⟩
    have headerAt : (headers ++ [header])[earlier.blocks.length + 1]? = some header := by
      rw [← lengthEq]
      exact List.getElem?_concat_length
    have tipAt : (headers ++ [header])[earlier.blocks.length]? = some tip :=
      getElem?_append_of_eq_some _ tipFound
    rw [ChainList.blocks_block]
    refine ⟨headers ++ [header], ⟨?_, getElem?_append_of_eq_some _ recorded.first, ?_⟩, ?_, ?_⟩
    · simp [lengthEq]
    · intro i block found
      by_cases old : i < earlier.blocks.length
      · rw [List.getElem?_append_left old] at found
        obtain ⟨parent, next, parentFound, nextFound, parentRoot, nextRoot⟩ :=
          recorded.listed i block found
        exact ⟨parent, next, getElem?_append_of_eq_some _ parentFound,
          getElem?_append_of_eq_some _ nextFound, parentRoot, nextRoot⟩
      · have last : i = earlier.blocks.length := by
          have := (List.getElem?_eq_some_iff.mp found).1
          simp at this
          omega
        subst last
        rw [List.getElem?_concat_length] at found
        cases found
        refine ⟨tip, header, tipAt, headerAt, ?_, BeaconBlock.hashTreeRoot_header bodyRooted⟩
        rw [← settled]
        exact parentRooted
    · intro forked member link linked
      rcases List.mem_append.mp member with old | new
      · exact (links _ old link linked).append _
      · obtain rfl := List.mem_singleton.mp new
        change link ∈ rootLinks after at linked
        rw [sameLinks] at linked
        exact (links _ earlier.last_mem_states link linked).append _
    · refine ⟨header, ?_, fun zero => ?_, fun zero => ?_, .inr ⟨headerEq, afterRooted, ?_, ?_⟩⟩
      · simpa using headerAt
      · change signed.message.stateRoot = Vector.replicate 32 0 at zero
        rw [zero] at afterRooted
        exact afterNonzero afterRooted
      · change after.slot = 0 at zero
        rw [frameSlot, ← slotEq] at zero
        rw [zero] at newer
        exact absurd newer UInt64.not_lt_zero
      · change signed.message.slot = after.slot
        rw [frameSlot, slotEq]
      · intro root read
        change getBlockRootAtSlot after (after.slot - 1) = .ok root at read
        rw [getBlockRootAtSlot_congr frameSlot roots, frameSlot] at read
        exact ⟨earlier.blocks.length, tip, by simp, tipAt, settledRead root read⟩

/-! ## Roots ordered along two chains -/

section TwoChains

variable {genesis : BeaconBlockHeader}
  {blocks : Bool → List ((fork : Fork) × BeaconBlock preset fork)}
  {headers : Bool → List BeaconBlockHeader}

/-- Some header after a block of one of two chains has the root, and `older` comes at or before it.
-/
private def DescendsFrom (blocks : Bool → List ((fork : Fork) × BeaconBlock preset fork))
    (headers : Bool → List BeaconBlockHeader) (older : (fork : Fork) × BeaconBlock preset fork)
    (root : Root) : Prop :=
  ∃ chain i a header, (headers chain)[i + 1]? = some header ∧
    SszType.hashTreeRoot header = .ok root ∧ a ≤ i ∧ (blocks chain)[a]? = some older

/-- Two chains that apply one block apply the same blocks at or before it.

The roots of the listed blocks must have no collision, and none may be the genesis header's root.
-/
private theorem appliesAtOrBefore_of_eq
    (recorded : ∀ chain, RecordedHeaders genesis (blocks chain) (headers chain))
    (unique : ∀ (chain chain' : Bool) (i j : Nat)
      (block block' : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block →
      (blocks chain')[j]? = some block' → ∀ root, SszType.hashTreeRoot block.2 = .ok root →
        SszType.hashTreeRoot block'.2 = .ok root → block = block')
    (notGenesis : ∀ (chain : Bool) (i : Nat) (block : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block → ∀ root,
      SszType.hashTreeRoot block.2 = .ok root → SszType.hashTreeRoot genesis ≠ .ok root) :
    ∀ (p q : Nat) {chain chain' : Bool} {block older : (fork : Fork) × BeaconBlock preset fork},
      (blocks chain)[p]? = some block → (blocks chain')[q]? = some block →
      ∀ a ≤ p, (blocks chain)[a]? = some older →
        ∃ a' ≤ q, (blocks chain')[a']? = some older
  | p, q, chain, chain', block, older, found, found', a, le, olderFound => by
    by_cases same : a = p
    · subst same
      rw [found] at olderFound
      cases olderFound
      exact ⟨q, le_rfl, found'⟩
    obtain ⟨p, rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    obtain ⟨parent, -, parentFound, -, parentRoot, -⟩ := (recorded chain).listed _ _ found
    obtain ⟨parent', -, parentFound', -, parentRoot', -⟩ := (recorded chain').listed _ _ found'
    obtain ⟨previous, previousFound, previousRoot⟩ :=
      (recorded chain).block_of_succ parentFound
    rw [parentRoot] at previousRoot
    rcases q with _ | q
    · rw [(recorded chain').first] at parentFound'
      cases parentFound'
      exact absurd parentRoot' (notGenesis _ _ _ previousFound _ previousRoot.symm)
    obtain ⟨previous', previousFound', previousRoot'⟩ :=
      (recorded chain').block_of_succ parentFound'
    rw [parentRoot'] at previousRoot'
    have equal := unique _ _ _ _ _ _ previousFound previousFound' _ previousRoot.symm
      previousRoot'.symm
    subst equal
    obtain ⟨a', le', found''⟩ := appliesAtOrBefore_of_eq recorded unique notGenesis p q
      previousFound previousFound' a (by omega) olderFound
    exact ⟨a', by omega, found''⟩

/-- A link along the headers of either chain keeps a root after the block `older`.

The roots of the listed blocks must have no collision, and none may be the genesis header's root.

No listed block may have the zero root. -/
private theorem DescendsFrom.of_linkAlong
    (recorded : ∀ chain, RecordedHeaders genesis (blocks chain) (headers chain))
    (unique : ∀ (chain chain' : Bool) (i j : Nat)
      (block block' : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block →
      (blocks chain')[j]? = some block' → ∀ root, SszType.hashTreeRoot block.2 = .ok root →
        SszType.hashTreeRoot block'.2 = .ok root → block = block')
    (notGenesis : ∀ (chain : Bool) (i : Nat) (block : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block → ∀ root,
      SszType.hashTreeRoot block.2 = .ok root → SszType.hashTreeRoot genesis ≠ .ok root)
    (notZero : ∀ (chain : Bool) (i : Nat) (block : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block →
      SszType.hashTreeRoot block.2 ≠ .ok (Vector.replicate 32 0))
    {older : (fork : Fork) × BeaconBlock preset fork} {link : Root × Root}
    (descends : DescendsFrom blocks headers older link.1)
    (along : ∃ chain, LinkAlong (headers chain) link) :
    DescendsFrom blocks headers older link.2 := by
  obtain ⟨chain, i, a, header, found, root, le, olderFound⟩ := descends
  obtain ⟨block, blockFound, blockRoot⟩ := (recorded chain).block_of_succ found
  rw [root] at blockRoot
  obtain ⟨chain', same | ⟨j, parent, next, parentFound, nextFound, parentRoot, nextRoot⟩ |
    ⟨zero, -⟩⟩ := along
  · rw [← same]
    exact ⟨chain, i, a, header, found, root, le, olderFound⟩
  · rcases j with _ | j
    · rw [(recorded chain').first] at parentFound
      cases parentFound
      exact absurd parentRoot (notGenesis _ _ _ blockFound _ blockRoot.symm)
    obtain ⟨block', blockFound', blockRoot'⟩ := (recorded chain').block_of_succ parentFound
    rw [parentRoot] at blockRoot'
    have equal := unique _ _ _ _ _ _ blockFound blockFound' _ blockRoot.symm blockRoot'.symm
    subst equal
    obtain ⟨a', le', found'⟩ :=
      appliesAtOrBefore_of_eq recorded unique notGenesis i j blockFound blockFound' a le olderFound
    exact ⟨chain', j + 1, a', next, nextFound, nextRoot, by omega, found'⟩
  · rw [zero] at blockRoot
    exact absurd blockRoot.symm (notZero _ _ _ blockFound)

end TwoChains

open scoped Classical in
/-- Accountable safety for two chains given as lists from one genesis state, with the hash events.

Each step must meet a stake bound, and each listed block must hold the root of the state after it.

If two listed finalized blocks conflict, the slashable stake is at least a guaranteed intersection.

Or two recorded headers share a root, or a listed block or a recorded state has the zero root. -/
theorem accountable_safety_isSlashableAttestationData_of_chainLists
    -- An epoch must have at least one slot, and the buffer of roots must cover three epochs.
    (positive : 0 < preset.SLOTS_PER_EPOCH.toNat)
    (window : 3 * preset.SLOTS_PER_EPOCH.toNat ≤ preset.SLOTS_PER_HISTORICAL_ROOT.toNat)
    -- The seed lookahead must leave room in the buffer of RANDAO mixes.
    (apart : preset.MIN_SEED_LOOKAHEAD.toNat + 2 < preset.EPOCHS_PER_HISTORICAL_VECTOR.toNat)
    {fork : Fork} {state : BeaconState preset fork} {eth1BlockHash : Hash32}
    {eth1Timestamp : UInt64} {deposits : Array Deposit}
    -- The genesis state built from deposits exists only before Altair.
    (before : fork < .altair)
    (computed :
      initializeBeaconStateFromEth1 config checks eth1BlockHash eth1Timestamp deposits before =
        .ok state)
    {last₁ last₂ : ForkedBeaconState preset}
    -- Each list ends at its last state, `last₁` or `last₂`.
    (chain₁ : ChainList config checks ⟨fork, state⟩ last₁)
    (chain₂ : ChainList config checks ⟨fork, state⟩ last₂)
    -- Each step of each list must meet the bound on the stake.
    (large₁ : ∀ step ∈ chain₁.steps, step.2.state.slot ≠ step.1.state.slot →
      (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt step.1.state index.toNat)
          (getActiveValidatorIndices step.1.state (getCurrentEpoch step.1.state)).toFinset)
    (large₂ : ∀ step ∈ chain₂.steps, step.2.state.slot ≠ step.1.state.slot →
      (step.1.state.slot + 1) % preset.SLOTS_PER_EPOCH = 0 →
      3 * preset.EFFECTIVE_BALANCE_INCREMENT.toNat <
        2 * stake (fun index => balanceAt step.1.state index.toNat)
          (getActiveValidatorIndices step.1.state (getCurrentEpoch step.1.state)).toFinset)
    -- The state root of each listed block must be the root of the state after it.
    (stateRooted₁ : ∀ applied ∈ chain₁.appliedBlocks,
      SszType.hashTreeRoot applied.after = .ok applied.signed.message.stateRoot)
    (stateRooted₂ : ∀ applied ∈ chain₂.appliedBlocks,
      SszType.hashTreeRoot applied.after = .ok applied.signed.message.stateRoot)
    -- `F₁` and `F₂` are listed blocks of the two lists.
    --
    -- Their roots are the roots of the two finalized checkpoints.
    {F₁ F₂ : (fork : Fork) × BeaconBlock preset fork}
    (listed₁ : F₁ ∈ chain₁.blocks)
    (rooted₁ : SszType.hashTreeRoot F₁.2 = .ok last₁.state.finalizedCheckpoint.root)
    (listed₂ : F₂ ∈ chain₂.blocks)
    (rooted₂ : SszType.hashTreeRoot F₂.2 = .ok last₂.state.finalizedCheckpoint.root)
    -- Neither list may apply one of them at or before the other, blocks compared as messages.
    (conflicting : ¬chain₁.AppliesAtOrBefore F₁ F₂ ∧ ¬chain₂.AppliesAtOrBefore F₁ F₂ ∧
      ¬chain₁.AppliesAtOrBefore F₂ F₁ ∧ ¬chain₂.AppliesAtOrBefore F₂ F₁) :
    -- Then validators are slashable, with the bound of the guaranteed intersection.
    --
    -- The checkpoints `l` and `r` and the bound are as for the order of the two lists' roots.
    (∃ l r : Models.Ffg.Checkpoint (StatesRoot (chain₁.states ++ chain₂.states)),
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ l.epoch ∧
      l.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      min last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ≤ r.epoch ∧
      r.epoch ≤ max last₁.state.finalizedCheckpoint.epoch.toNat
        last₂.state.finalizedCheckpoint.epoch.toNat ∧
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c ∪
              chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c)
            (ffgVotes (toStatesRoot (chain₁.states ++ chain₂.states))
              (chain₁.votes ∪ chain₂.votes)) s t)
        (toStatesRoot (chain₁.states ++ chain₂.states) (Vector.replicate 32 0)) l ∧
      JustifiedBy (fun s t => ∃ last ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
          SlackLink (fun c => activeSetAt last.state c.epoch)
            (fun c => activeSetAt last.state (c.epoch + 1))
            (fun c => chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c ∪
              chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) c)
            (ffgVotes (toStatesRoot (chain₁.states ++ chain₂.states))
              (chain₁.votes ∪ chain₂.votes)) s t)
        (toStatesRoot (chain₁.states ++ chain₂.states) (Vector.replicate 32 0)) r ∧
      ∃ a ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      ∃ b ∈ ({last₁, last₂} : Set (ForkedBeaconState preset)),
      ∃ wl ∈ chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) l ∪
        chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) l,
      ∃ wr ∈ chain₁.balances (toStatesRoot (chain₁.states ++ chain₂.states)) r ∪
        chain₂.balances (toStatesRoot (chain₁.states ++ chain₂.states)) r,
        guaranteedIntersection (activeSetAt a.state l.epoch) (activeSetAt a.state (l.epoch + 1))
            (activeSetAt b.state r.epoch) (activeSetAt b.state (r.epoch + 1)) wl wr ≤
          stake wl {validator ∈ activeSetAt a.state l.epoch ∩ activeSetAt b.state r.epoch |
            ∃ data1 data2,
              (validator, data1) ∈ chain₁.votes ∪ chain₂.votes ∧
              (validator, data2) ∈ chain₁.votes ∪ chain₂.votes ∧
              isSlashableAttestationData data1 data2 = true} ∧
        guaranteedIntersection (activeSetAt b.state r.epoch) (activeSetAt b.state (r.epoch + 1))
            (activeSetAt a.state l.epoch) (activeSetAt a.state (l.epoch + 1)) wr wl ≤
          stake wr {validator ∈ activeSetAt b.state r.epoch ∩ activeSetAt a.state l.epoch |
            ∃ data1 data2,
              (validator, data1) ∈ chain₁.votes ∪ chain₂.votes ∧
              (validator, data2) ∈ chain₁.votes ∪ chain₂.votes ∧
              isSlashableAttestationData data1 data2 = true}) ∨
    -- Or two different headers that the two chains record have one root.
    --
    -- These headers are the genesis header and the headers of the listed blocks.
    --
    -- The genesis header is the latest block header of the genesis state, with the state's root.
    --
    -- The root of the header of a listed block is the root of the block.
    --
    -- So the blocks stand for the headers.
    ((∃ block ∈ chain₁.blocks ++ chain₂.blocks, ∃ block' ∈ chain₁.blocks ++ chain₂.blocks,
        block ≠ block' ∧ ∃ root, SszType.hashTreeRoot block.2 = .ok root ∧
          SszType.hashTreeRoot block'.2 = .ok root) ∨
      -- A listed block comes after slot zero, so its header is never the genesis header.
      ∃ block ∈ chain₁.blocks ++ chain₂.blocks, ∃ genesisRoot root,
        SszType.hashTreeRoot state = .ok genesisRoot ∧
        SszType.hashTreeRoot { state.latestBlockHeader with stateRoot := genesisRoot } =
          .ok root ∧
        SszType.hashTreeRoot block.2 = .ok root) ∨
    -- Or a listed block has the zero root, or a state that the chains record has it.
    --
    -- These states are the genesis state and the state after each listed block.
    ((∃ block ∈ chain₁.blocks ++ chain₂.blocks,
        SszType.hashTreeRoot block.2 = .ok (Vector.replicate 32 0)) ∨
      SszType.hashTreeRoot state = .ok (Vector.replicate 32 0) ∨
      ∃ applied ∈ chain₁.appliedBlocks ++ chain₂.appliedBlocks,
        SszType.hashTreeRoot applied.after = .ok (Vector.replicate 32 0)) := by
  refine (Classical.em _).elim (fun events => .inr events) (fun events => .inl ?_)
  refine accountable_safety_isSlashableAttestationData_of_statesRoot positive window apart
    before computed chain₁ chain₂ large₁ large₂ ?_
  -- Without a hash event, the two finalized blocks conflict in the order of the lists' roots.
  --
  -- So two blocks that conflict on the two chains conflict in the order of the two lists' roots.
  obtain ⟨genesisRoot, rooted⟩ : ∃ root, SszType.hashTreeRoot state = .ok root := by
    rcases ChainList.genesisRooted computed chain₁ with ⟨-, empty⟩ | rooted
    · rw [empty] at listed₁
      cases listed₁
    · exact rooted
  let blocks : Bool → List ((fork : Fork) × BeaconBlock preset fork) :=
    fun chain => cond chain chain₁.blocks chain₂.blocks
  have listed : ∀ (chain : Bool) (i : Nat) (block : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block →
      block ∈ chain₁.blocks ++ chain₂.blocks := by
    intro chain i block found
    cases chain
    · exact List.mem_append_right _ (List.mem_of_getElem? found)
    · exact List.mem_append_left _ (List.mem_of_getElem? found)
  have unique : ∀ (chain chain' : Bool) (i j : Nat)
      (block block' : (fork : Fork) × BeaconBlock preset fork), (blocks chain)[i]? = some block →
      (blocks chain')[j]? = some block' → ∀ root, SszType.hashTreeRoot block.2 = .ok root →
        SszType.hashTreeRoot block'.2 = .ok root → block = block' := by
    intro chain chain' i j block block' found found' root blockRoot blockRoot'
    by_contra different
    exact events (.inl (.inl ⟨block, listed _ _ _ found, block', listed _ _ _ found', different,
      root, blockRoot, blockRoot'⟩))
  have notGenesis : ∀ (chain : Bool) (i : Nat) (block : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block → ∀ root,
      SszType.hashTreeRoot block.2 = .ok root →
        SszType.hashTreeRoot { state.latestBlockHeader with stateRoot := genesisRoot } ≠
          .ok root := by
    intro chain i block found root blockRoot genesisHeaderRoot
    exact events (.inl (.inr ⟨block, listed _ _ _ found, genesisRoot, root, rooted,
      genesisHeaderRoot, blockRoot⟩))
  have notZero : ∀ (chain : Bool) (i : Nat) (block : (fork : Fork) × BeaconBlock preset fork),
      (blocks chain)[i]? = some block →
      SszType.hashTreeRoot block.2 ≠ .ok (Vector.replicate 32 0) := fun chain i block found zero =>
    events (.inr (.inl ⟨block, listed _ _ _ found, zero⟩))
  have nonzero : genesisRoot ≠ Vector.replicate 32 0 := fun zero => by
    rw [zero] at rooted
    exact events (.inr (.inr (.inl rooted)))
  have nonzeroAfter : ∀ applied ∈ chain₁.appliedBlocks ++ chain₂.appliedBlocks,
      SszType.hashTreeRoot applied.after ≠ .ok (Vector.replicate 32 0) :=
    fun applied member zero => events (.inr (.inr (.inr ⟨applied, member, zero⟩)))
  -- Without these events, each root that a state of the two chains records is a recorded header's.
  obtain ⟨headers₁, recorded₁, links₁, -⟩ := chain₁.recordedHeaders computed rooted nonzero
    stateRooted₁ fun applied member => nonzeroAfter applied (List.mem_append_left _ member)
  obtain ⟨headers₂, recorded₂, links₂, -⟩ := chain₂.recordedHeaders computed rooted nonzero
    stateRooted₂ fun applied member => nonzeroAfter applied (List.mem_append_right _ member)
  let headers : Bool → List BeaconBlockHeader := fun chain => cond chain headers₁ headers₂
  have recorded : ∀ chain, RecordedHeaders { state.latestBlockHeader with stateRoot := genesisRoot }
      (blocks chain) (headers chain) := fun chain => by
    cases chain
    · exact recorded₂
    · exact recorded₁
  -- Two consecutive slots then record one header twice, or a header and the next one on the chain.
  --
  -- So the links of the two chains order a root before another only along a chain, by parent roots.
  --
  -- An order of two roots along the links of the lists keeps every root after the first block.
  have descends : ∀ {older : (fork : Fork) × BeaconBlock preset fork} {start finish : Root},
      toStatesRoot (chain₁.states ++ chain₂.states) start ≤
        toStatesRoot (chain₁.states ++ chain₂.states) finish →
      DescendsFrom blocks headers older start → DescendsFrom blocks headers older finish := by
    intro older start finish le from'
    change Relation.ReflTransGen (fun older newer => ∃ forked ∈ chain₁.states ++ chain₂.states,
      (older, newer) ∈ rootLinks forked.state) start finish at le
    induction le with
    | refl => exact from'
    | tail _ linked descends' =>
      obtain ⟨forked, member, linked⟩ := linked
      refine DescendsFrom.of_linkAlong (link := (_, _)) recorded unique notGenesis notZero
        descends' ?_
      rcases List.mem_append.mp member with one | two
      · exact ⟨true, links₁ forked one _ linked⟩
      · exact ⟨false, links₂ forked two _ linked⟩
  -- A listed block starts the order, and a listed block that ends it comes after it on a chain.
  have start : ∀ (chain : Bool) (i : Nat) {block : (fork : Fork) × BeaconBlock preset fork}
      {root : Root},
      (blocks chain)[i]? = some block → SszType.hashTreeRoot block.2 = .ok root →
        DescendsFrom blocks headers block root := by
    intro chain i block root found blockRoot
    obtain ⟨-, header, -, headerFound, -, headerRoot⟩ := (recorded chain).listed i block found
    exact ⟨chain, i, i, header, headerFound, headerRoot.trans blockRoot, le_rfl, found⟩
  have finish : ∀ (chain : Bool) (j : Nat) {older block : (fork : Fork) × BeaconBlock preset fork}
      {root : Root},
      (blocks chain)[j]? = some block → SszType.hashTreeRoot block.2 = .ok root →
        DescendsFrom blocks headers older root →
          ∃ (chain' : Bool) (i a : Nat), a ≤ i ∧ (blocks chain')[a]? = some older ∧
            (blocks chain')[i]? = some block := by
    intro chain j older block root found blockRoot from'
    obtain ⟨chain', i, a, header, headerFound, headerRoot, le, olderFound⟩ := from'
    obtain ⟨block', found', blockRoot'⟩ := (recorded chain').block_of_succ headerFound
    rw [headerRoot] at blockRoot'
    have equal := unique _ _ _ _ _ _ found' found _ blockRoot'.symm blockRoot
    subst equal
    exact ⟨chain', i, a, le, olderFound, found'⟩
  obtain ⟨i₁, found₁⟩ := List.mem_iff_getElem?.mp listed₁
  obtain ⟨i₂, found₂⟩ := List.mem_iff_getElem?.mp listed₂
  refine ⟨fun le => ?_, fun le => ?_⟩
  · obtain ⟨chain, i, a, le', olderFound, found⟩ := finish false i₂ found₂ rooted₂
      (descends le (start true i₁ found₁ rooted₁))
    cases chain
    · exact conflicting.2.1 ⟨a, i, le', olderFound, found⟩
    · exact conflicting.1 ⟨a, i, le', olderFound, found⟩
  · obtain ⟨chain, i, a, le', olderFound, found⟩ := finish true i₁ found₁ rooted₁
      (descends le (start false i₂ found₂ rooted₂))
    cases chain
    · exact conflicting.2.2.2 ⟨a, i, le', olderFound, found⟩
    · exact conflicting.2.2.1 ⟨a, i, le', olderFound, found⟩

end EthLib.Consensus
