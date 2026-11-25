include "../src/matrices.dfy"

// DEMO of src/matrices.dfy: squaring a concrete nat matrix and reading its trace,
// exercising NatMatrices1's pow and trace. Moved out of src/ (it was a Main test
// module) into the examples, as an @Test for `dafny test`.
module TestMatrices {
    import opened NatMatrices1

    @Test
    method test() {
        var a := new nat[2, 2]((i, j) => i + j);                    // [[0,1],[1,2]]
        var sq := pow(a, 2);                                        // a*a == [[1,2],[2,5]]
        print "\n", sq[0,0], " ", sq[0,1], " ", sq[1,0], " ", sq[1,1];
        var t := trace(sq);                                         // 1 + 5 == 6
        print "\ntrace = ", t;
    }
}
