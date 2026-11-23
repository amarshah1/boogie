// Two children zero disjoint slices of a contiguous 1D tensor and signal back their memory.
const unique tid_0: Tid;
const unique tid_1: Tid;

yield procedure {:layer 1} Main(
    {:linear_in} init_sem_id: One SemId, {:linear_in} init_signals: UnitMap (One SemSignal),
    {:linear} wait: One SemWait, {:linear_in} init_mem: Map (One MemId) Value,
    tensor: Tensor1D, k: int)
    returns ({:linear} sem_id: One SemId, {:linear} signals: UnitMap (One SemSignal),
             {:linear} mem: Map (One MemId) Value)
requires {:layer 1} wait->val->sem_id == init_sem_id->val;
requires {:layer 1} AllSemaphoreSignals(init_sem_id, init_signals);
requires {:layer 1} Vals(init_mem->dom) == Tensor1DAddrs(tensor);
requires {:layer 1} 0 <= k && k <= tensor->dim0;
requires {:layer 1} tensor->stride0 == 1;
preserves call SemaphoreInv();
ensures {:layer 1} sem_id == init_sem_id;
ensures {:layer 1} AllSemaphoreSignals(sem_id, signals);
ensures {:layer 1} Set_IsSubset(Tensor1DAddrs(Slice1D(tensor, 0, k)), Vals(mem->dom));
ensures {:layer 1} Set_IsSubset(Tensor1DAddrs(Slice1D(tensor, k, tensor->dim0 - k)), Vals(mem->dom));
{
    var slice_0, slice_1: Tensor1D;
    var ids_0, ids_1: [One MemId]bool;
    var mem_0, mem_1, returned_mem: Map (One MemId) Value;
    var done: UnitMap (One SemSignal);
    var shares: UnitMap (One MemShare);
    var signal_0, signal_1: One SemSignal;
    var awaited: [One SemSignal]bool;
    var expected_mem_ids: Map SemSignal ([One MemId]bool);
    var expected_mem_shares: Map SemSignal ([One MemShare]bool);

    slice_0 := Slice1D(tensor, 0, k);
    slice_1 := Slice1D(tensor, k, tensor->dim0 - k);
    ids_0 := Ones(Tensor1DAddrs(slice_0));
    ids_1 := Ones(Tensor1DAddrs(slice_1));
    mem := init_mem;
    assume {:layer 1} (forall {:pool "A"} x: int ::
        (exists y: int :: {:add_to_pool "Tensor1DIndex", x, x + k} true));
    call mem, mem_0 := Map_Split_Wrapper(mem, Tensor1DAddrs(tensor), Tensor1DAddrs(slice_0));
    call mem, mem_1 := Map_Split_Wrapper(mem,
        Set_Difference(Tensor1DAddrs(tensor), Tensor1DAddrs(slice_0)), Tensor1DAddrs(slice_1));
    assume false;
    signal_0 := One(SemSignal(init_sem_id->val, tid_0));
    signal_1 := One(SemSignal(init_sem_id->val, tid_1));
    awaited := Set_Add(Set_Singleton(signal_0), signal_1);
    expected_mem_ids := Map_Singleton(signal_0->val, ids_0);
    expected_mem_ids := Map_Update(expected_mem_ids, signal_1->val, ids_1);
    expected_mem_shares := Map_Singleton(signal_0->val, Set_Empty());
    expected_mem_shares := Map_Update(expected_mem_shares, signal_1->val, Set_Empty());
    call Publish(init_sem_id, awaited, expected_mem_ids, expected_mem_shares);
    signals := init_signals;
    call One_Get(signals, signal_0);
    call One_Get(signals, signal_1);
    async call Child(signal_0, mem_0, slice_0);
    async call Child(signal_1, mem_1, slice_1);
    call SemaphoreInv() | SemaphoreWaitInv(wait) |
         ExpectedSemaphoreContentsInv(wait, awaited, expected_mem_ids, expected_mem_shares);
    call sem_id, done, returned_mem, shares := Wait(wait);
    call Map_Join(signals, done);
    call Map_Join(mem, returned_mem);
}

yield invariant {:layer 1} ChildExpectedMemInv(
    {:linear} signal: One SemSignal, {:linear} mem: Map (One MemId) Value);
preserves Map_Contains(semaphores, One(signal->val->sem_id));
preserves Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_ids, signal->val);
preserves Map_At(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_ids, signal->val) == mem->dom;
preserves Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_shares, signal->val);
preserves Map_At(Map_At(semaphores, One(signal->val->sem_id))->expected_mem_shares, signal->val) == Set_Empty();
free preserves !Map_Contains(Map_At(semaphores, One(signal->val->sem_id))->done, signal);

yield procedure {:layer 1} Child(
    {:linear_in} signal: One SemSignal, {:linear_in} init_mem: Map (One MemId) Value,
    tensor: Tensor1D)
requires {:layer 1} Vals(init_mem->dom) == Tensor1DAddrs(tensor);
requires {:layer 1} 0 <= tensor->dim0;
requires call SemaphoreSignalInv(signal);
requires call ChildExpectedMemInv(signal, init_mem);
preserves call SemaphoreInv();
{
    var mem: Map (One MemId) Value;
    var shares: UnitMap (One MemShare);
    var i: int;

    mem := init_mem;
    i := 0;
    while (i < tensor->dim0)
        invariant {:yields} true;
        invariant {:layer 1} 0 <= i && i <= tensor->dim0;
        invariant {:layer 1} Vals(mem->dom) == Tensor1DAddrs(tensor);
        invariant call SemaphoreInv();
        invariant call SemaphoreSignalInv(signal);
        invariant call ChildExpectedMemInv(signal, mem);
    {
        call mem := WriteMemory(mem, tensor->start + i * tensor->stride0);
        i := i + 1;
    }
    call shares := Map_MakeEmpty();
    call Signal(signal, mem, shares);
}

pure action WriteMemory({:linear_in} init_mem: Map (One MemId) Value, location: MemId)
    returns ({:linear} mem: Map (One MemId) Value)
{
    mem := init_mem;
    assert Map_Contains(mem, One(location));
    call Path_Store(mem->val[One(location)], 0);
}
