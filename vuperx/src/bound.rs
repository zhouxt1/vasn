//! Upper bounds on encoded size.
//!
//! `enc_bound(w, e, m)` says every value the format accepts encodes into at
//! most `m` bits. It started out load-bearing for correctness: an open type
//! states its content's length in octets, a single length determinant tops
//! out just under 16K (§11.9), and without a size bound `open_type` could not
//! be shown to be a format at all.
//!
//! Implementing fragmentation (§11.9.3.8, `frag.rs`) removed that need --
//! `lemma_open_format` now has no size hypothesis, because content of any
//! length is carried by a fragmenting determinant. What survives is buffer
//! sizing: an encoder still has to know how large an output to allocate, and
//! that is what these lemmas answer.
//!
//! One bound lemma per combinator -- `uint` is `n`, `pair` adds, `list(n)`
//! multiplies, `sized(lb..ub)` is the determinant plus `ub` elements -- and
//! the compiler emits the arithmetic per type.
use vstd::prelude::*;
use crate::format::*;
use crate::prim::*;
use crate::opt::*;
use crate::list::*;
use crate::bitspec::*;

verus! {

pub open spec fn enc_bound<A>(w: Wf<A>, e: Enc<A>, m: nat) -> bool {
    forall|a: A| w(a) ==> #[trigger] e(a).len() <= m
}

/// A bound may always be weakened, which is what lets a CHOICE take the
/// maximum over its alternatives and a SEQUENCE round its fields up.
pub proof fn lemma_bound_mono<A>(w: Wf<A>, e: Enc<A>, m: nat, m2: nat)
    requires enc_bound(w, e, m), m <= m2,
    ensures enc_bound(w, e, m2),
{
}

pub proof fn lemma_uint_bound(n: nat)
    ensures enc_bound(uint_wf(n), uint_enc(n), n),
{
    assert forall|v: u64| uint_wf(n)(v) implies #[trigger] uint_enc(n)(v).len() <= n by {
        lemma_uint_enc_len(n, v);
    }
}

pub proof fn lemma_map_bound<A, B>(wa: Wf<A>, ea: Enc<A>, to: spec_fn(A) -> B,
                                   from: spec_fn(B) -> A, m: nat)
    requires enc_bound(wa, ea, m),
    ensures enc_bound(map_wf(wa, to, from), map_enc(ea, from), m),
{
    assert forall|b: B| map_wf(wa, to, from)(b) implies
        #[trigger] map_enc(ea, from)(b).len() <= m
    by {
        lemma_map_wf_val(wa, to, from, b);
        lemma_map_enc_val(ea, from, b);
    }
}

pub proof fn lemma_restrict_bound<A>(w: Wf<A>, e: Enc<A>, p: spec_fn(A) -> bool, m: nat)
    requires enc_bound(w, e, m),
    ensures enc_bound(restrict_wf(w, p), e, m),
{
    assert forall|a: A| restrict_wf(w, p)(a) implies #[trigger] e(a).len() <= m by {
        lemma_restrict_wf_val(w, p, a);
    }
}

pub proof fn lemma_pair_bound<A, B>(w1: Wf<A>, e1: Enc<A>, m1: nat,
                                    w2: Wf<B>, e2: Enc<B>, m2: nat)
    requires enc_bound(w1, e1, m1), enc_bound(w2, e2, m2),
    ensures enc_bound(pair_wf(w1, w2), pair_enc(e1, e2), (m1 + m2) as nat),
{
    assert forall|p: (A, B)| pair_wf(w1, w2)(p) implies
        #[trigger] pair_enc(e1, e2)(p).len() <= m1 + m2
    by {
        lemma_pair_wf_val(w1, w2, p.0, p.1);
        lemma_pair_enc_val(e1, e2, p.0, p.1);
        assert(p == (p.0, p.1));
    }
}

pub proof fn lemma_dep_bound<A, B>(w1: Wf<A>, e1: Enc<A>, m1: nat,
                                   w2: spec_fn(A) -> Wf<B>, e2: spec_fn(A) -> Enc<B>, m2: nat)
    requires
        enc_bound(w1, e1, m1),
        forall|a: A| w1(a) ==> enc_bound(#[trigger] w2(a), e2(a), m2),
    ensures enc_bound(dep_wf(w1, w2), dep_enc(e1, e2), (m1 + m2) as nat),
{
    assert forall|p: (A, B)| dep_wf(w1, w2)(p) implies
        #[trigger] dep_enc(e1, e2)(p).len() <= m1 + m2
    by {
        lemma_dep_wf_val(w1, w2, p.0, p.1);
        lemma_dep_enc_val(e1, e2, p.0, p.1);
        assert(enc_bound(w2(p.0), e2(p.0), m2));
        assert(p == (p.0, p.1));
    }
}

pub proof fn lemma_opt_bound<A>(present: bool, w: Wf<A>, e: Enc<A>, m: nat)
    requires enc_bound(w, e, m),
    ensures enc_bound(opt_wf(present, w), opt_enc(present, e), m),
{
    assert forall|o: Option<A>| opt_wf(present, w)(o) implies
        #[trigger] opt_enc(present, e)(o).len() <= m
    by {
        lemma_opt_wf_val(present, w, o);
        lemma_opt_enc_val(present, e, o);
    }
}

pub proof fn lemma_unit_bound<A>(a0: A)
    ensures enc_bound(unit_wf(a0), unit_enc::<A>(), 0nat),
{
    assert forall|a: A| unit_wf(a0)(a) implies #[trigger] unit_enc::<A>()(a).len() <= 0nat by {
        lemma_unit_enc_val(a);
    }
}

// ------------------------------------------------------------------- lists

pub proof fn lemma_list_enc_rec_bound<A>(l: Seq<A>, w: Wf<A>, e: Enc<A>, m: nat)
    requires enc_bound(w, e, m), forall|i: int| 0 <= i < l.len() ==> w(#[trigger] l[i]),
    ensures list_enc_rec(l, e).len() <= l.len() * m,
    decreases l.len(),
{
    if l.len() == 0 {
        assert(list_enc_rec(l, e) =~= Seq::<bool>::empty());
    } else {
        assert forall|i: int| 0 <= i < l.skip(1).len() implies w(#[trigger] l.skip(1)[i]) by {
            assert(l.skip(1)[i] == l[i + 1]);
        }
        lemma_list_enc_rec_bound(l.skip(1), w, e, m);
        assert(e(l[0]).len() <= m);
        assert(l.skip(1).len() == l.len() - 1);
        assert((l.len() - 1) * m + m == l.len() * m) by (nonlinear_arith)
            requires l.len() >= 1;
        {}
    }
}

pub proof fn lemma_list_bound<A>(n: nat, w: Wf<A>, e: Enc<A>, m: nat)
    requires enc_bound(w, e, m),
    ensures enc_bound(list_wf(n, w), list_enc(n, e), (n * m) as nat),
{
    assert forall|l: Seq<A>| list_wf(n, w)(l) implies #[trigger] list_enc(n, e)(l).len() <= n * m
    by {
        lemma_list_wf_val(n, w, l);
        lemma_list_enc_val(n, e, l);
        lemma_list_enc_rec_bound(l, w, e, m);
    }
}

/// SIZE (lb..ub) OF: the determinant, then at most `ub` elements.
pub proof fn lemma_sized_bound<A>(lb: nat, ub: nat, n: nat, w: Wf<A>, e: Enc<A>, m: nat)
    requires enc_bound(w, e, m), lb <= ub, ub < p2(56),
    ensures enc_bound(sized_wf(lb, ub, n, w), sized_enc(lb, ub, n, e), (n + ub * m) as nat),
{
    assert forall|c: u64| ulen_wf(lb, ub, n)(c) implies
        enc_bound(#[trigger] list_wf_f(w)(c), list_enc_f(e)(c), (ub * m) as nat)
    by {
        lemma_ulen_wf_bound(lb, ub, n, c);
        lemma_list_bound(c as nat, w, e, m);
        assert((c as nat) * m <= ub * m) by (nonlinear_arith)
            requires (c as nat) <= ub;
        {}
        lemma_bound_mono(list_wf(c as nat, w), list_enc(c as nat, e), (c as nat * m) as nat,
                         (ub * m) as nat);
    }
    assert forall|x: u64| ulen_wf(lb, ub, n)(x) implies
        #[trigger] ulen_enc(lb, ub, n)(x).len() <= n
    by {
        lemma_map_wf_val(ulen_base_wf(lb, ub, n), ulen_to(lb), ulen_from(lb), x);
        lemma_map_enc_val(uint_enc(n), ulen_from(lb), x);
        lemma_uint_enc_len(n, ulen_from(lb)(x));
    }
    lemma_dep_bound(ulen_wf(lb, ub, n), ulen_enc(lb, ub, n), n,
                    list_wf_f(w), list_enc_f(e), (ub * m) as nat);
}

} // verus!
