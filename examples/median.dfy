include "../src/median.dfy"

// DEMO: computing medians over two different carriers from the same Medians
// interface -- ints (floor averaging) and bv8 bit vectors (shift-halving) --
// each a concrete refinement of src/median.dfy's abstract Medians module.
module TestMedians {
    import IM = IntMedian
    import BVM = BvMedian

    @Test
    method test() {
        var ints := [1,2,3,4,5];
        print "\nints := ", IM.Median(ints);
        var bvs: seq<bv8> := [1,2,3,4,5];
        print "\nbit vectors := ", BVM.Median(bvs);
    }
}
