(** * Fibonacci 
  Copyright INRIA (2014) Marelle Team (Jose Grimm).
*)


(* $Id: fibm.v,v 1.3 2018/07/13 05:59:59 grimm Exp $ *)

Set Warnings "-notation-overridden".
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path fintype.
From mathcomp Require Import div bigop binomial prime finset ssralg ssrnum ssrint.
Set Implicit Arguments.
Unset Strict Implicit.

(** ** Additional lemmas *)

(* Comparison *) 
Lemma ltn_paddl m n: 0 < m -> n < m + n.
Proof. by rewrite - (ltn_add2r n) add0n. Qed.

Lemma ltn_paddr m n: 0 < m -> n < n +m.
Proof. by move/(ltn_paddl n); rewrite addnC. Qed.

Lemma leq_BD n p : n - p <= n + p. 
Proof. exact:(leq_trans (leq_subr p n) (leq_addr p n)). Qed.

Lemma leqn1 n: (n <=1) = (n==0) || (n ==1).
Proof. by rewrite leq_eqVlt orbC ltnS leqn0. Qed.

(* Half *)
Lemma half_le1 m: m./2 <= m.
Proof. by rewrite -{2}(odd_double_half m) -addnn addnA leq_addl. Qed.

Lemma half_le2 m: (m.+1)./2 <= m.
Proof. by case: m => // m /=; rewrite ltnS half_le1. Qed.

Lemma half_le3 m: 1 < m ->  (m.+1)./2 < m.
Proof. by case: m => [|[|n _]] //;rewrite ltnS ltnS half_le2. Qed.

Lemma half_le3w m: 1 < m ->  m./2 < m.
Proof. move/half_le3 => h; exact: (leq_ltn_trans (half_leq (leqnSn m)) h). Qed.

Lemma half_le4 n: n <= n./2 -> n <= 1. 
Proof. by apply: contraLR; rewrite -!ltnNge; apply: half_le3w. Qed.

Lemma double_half_le m : m./2.*2 <= m.
Proof. by rewrite -{2}(odd_double_half m) leq_addl. Qed.

(* double *)
Lemma double_le1 n: n <= n.*2.
Proof. by rewrite -addnn leq_addl. Qed.

Lemma double_le2 n: n < n.*2.+1.
Proof. by rewrite ltnS double_le1. Qed.

Lemma double_le3 n: n.+1 < (n.+1).*2.
Proof. by rewrite doubleS !ltnS double_le1. Qed.

Lemma eqn_double m n: (m.*2 == n.*2) = (m == n).
Proof. by rewrite - !muln2 eqn_mul2r. Qed.

Lemma double_inj: injective (fun z  => z.*2).
Proof. apply:can_inj doubleK. Qed.

Lemma doubleS_inj: injective (fun z => z.*2.+1).
Proof. apply: inj_comp succn_inj  double_inj. Qed.


(* Odd *)

Lemma odd_sqr n: odd (n^2) = odd n.
Proof. by rewrite odd_exp. Qed.

Lemma odd_dichot n: n = (n./2).*2.+1 \/ n = (n./2).*2.
Proof. by rewrite -{1 3} (odd_double_half n);case: odd; [left | right]. Qed.

Lemma oddE n: odd n -> n = (n./2).*2.+1.
Proof. by rewrite -{2} (odd_double_half n) => ->. Qed.

Lemma evenE n: odd n = false -> n = (n./2).*2.
Proof. by rewrite -{2} (odd_double_half n) => ->. Qed.

Lemma cantor n : n < 2 ^n. 
Proof. exact: (ltn_expl n (ltnSn 1)). Qed.

Lemma expn2S n: 2^n.+1 = (2^n).*2.
Proof. by rewrite expnS mul2n. Qed.

Lemma rem_two_prop1 m i: (m.*2) %% (2 ^(i.+1)) = (m %% 2^i).*2.
Proof.  
rewrite {1}(divn_eq m (2^i)) doubleD doubleMr -expn2S modnMDl modn_small //. 
by rewrite expn2S ltn_double ltn_pmod // expn_gt0.
Qed.

Lemma rem_two_prop2 m i: (m.*2.+1) %% (2 ^(i.+1)) = (m %% 2^i).*2.+1.
Proof.  
rewrite {1}(divn_eq m (2^i)) doubleD doubleMr -expn2S - addnS modnMDl.
by rewrite modn_small // expn2S ltn_Sdouble ltn_pmod // expn_gt0.
Qed.

Lemma pow2_mod3 n: 2^n %% 3 = 1 + odd n.
Proof.
by elim:n => // n Hr /=; rewrite expnS -modnMm Hr; case: odd.
Qed.

Lemma pow2_mod3' n:
  2^n = if (odd n) then (3*(((2^n).-2) %/3)).+2 else (3*(((2^n).-1) %/3)).+1. 
Proof.
rewrite (divn_eq (2^n) 3) pow2_mod3 (mulnC _ 3).
by case: odd; rewrite !addnS addn0 /= mulKn.
Qed.

Lemma sqrnD_sub' m n: n <= m -> (m + n) ^ 2 =  4 * (m * n) + (m - n) ^ 2.
Proof.
move => h; rewrite sqrnD sqrn_sub // -[4]/(2+2) mulnDl - [in RHS]addnA addnC.
by rewrite subnKC // nat_Cauchy.
Qed.

(* sums *)


Lemma split_sum_even_odd1 (F: nat -> nat) n:
  \sum_(i<n.*2) (F i) = \sum_(i< n) (F i.*2) + \sum_(i< n) (F i.*2.+1).
Proof.
elim:n; first by rewrite !big_ord0.
by move => k Hr; rewrite doubleS !big_ord_recr /= Hr addnACA addnA.
Qed.

Lemma split_sum_even_odd (F: nat -> nat) n:
  \sum_(i<n) (F i) = \sum_(i< (n.+1)./2) (F i.*2) + \sum_(i< n./2) (F i.*2.+1).
Proof.
by  case:(odd_dichot n) => ->; rewrite (half_bit_double n./2 true) -? doubleS
   doubleK ? big_ord_recr split_sum_even_odd1  // addnAC. 
Qed.

Lemma sum_rcons a l (F: nat -> nat): 
  \sum_(i <- rcons l a) F i = F a + \sum_(i <- l) F i.
Proof.
by elim: l a => [a | a l Ih b]; rewrite /= !big_cons ?big_nil // Ih addnCA.
Qed.

Lemma sum_rev l (F: nat -> nat):
  \sum_(i <- rev l) F i = \sum_(i <- l) F i.
Proof. 
by elim: l => [|a l H]; rewrite ? big_nil // big_cons rev_cons sum_rcons H.
Qed.

Lemma big_nat_shift  a b c p F:
  \sum_(c + a <= i < c + b | p i)  F i = 
  \sum_(a <= i < b | p (c + i)) F (c + i).
Proof.
rewrite /index_iota subnDl unlock; elim: (b - a) {1 3} (a) => // i H d /=.
by rewrite  -addnS H. 
Qed.

Lemma big_nat_cond_eq  a b p p' F :
  (forall i, a <= i < b ->  (p i = p' i)) -> 
  \sum_(a <= i < b | p i) F i =  \sum_(a <= i < b | p' i) F i.
Proof.
rewrite big_nat_cond [in RHS] big_nat_cond => H; apply: eq_bigl => i.
by apply: (andb_id2l (H i)).
Qed.

(** A property of the totient function *)

Lemma coprime_if_bezout a b u v: u * a  = v * b + 1 -> coprime a b. 
Proof.
move => H; apply/coprimeP. 
  by move: H; case:(posnP a) => // ->; rewrite muln0 addn1.
by exists (u,v); rewrite /= H addKn.
Qed.

Lemma minimal_bezout a b: 0 < a -> 0 < b -> coprime a b ->
  exists u v, [/\ u * a  = v * b + 1,  v < a & u <= b].
Proof.
move => ap bp cab; move/(coprimeP b ap): cab => [p hp].
have : p.1 * a =  p.2 * b + 1.
  by move: (ltnSn 0); rewrite -{2 3} hp subn_gt0 => /ltnW h; rewrite subnKC.
rewrite (divn_eq p.2 a) mulnDl mulnAC -addnA => sa.
have la: p.2 %/ a * b  <= p.1 by rewrite -(leq_pmul2r ap) sa leq_addr.
move/eqP:sa; rewrite -{1} (subnKC la) mulnDl eqn_add2l => /eqP hc.
have va:= (ltn_pmod p.2 ap).
move: (va);rewrite -(ltn_pmul2r bp) -addn1- hc mulnC (leq_pmul2l ap) => hd.
by exists  (p.1 - p.2 %/ a * b), (p.2 %% a).
Qed.

Lemma minimal_bezout_prop a b u v: u * a  = v * b + 1 -> v < a -> u <= b ->
  (forall u' v', u' * a = v' * b +1 -> (u <= u') && (v <= v')).
Proof.
move => B ua vb u' v' B'.
have ap: 0 < a by move:ua; case:(a).
case (posnP b) => bp. 
  by move: vb B; rewrite bp leqn0 => /eqP ->; rewrite muln0.
case: (ltnP u' u) => cp; last first.
  by rewrite -(leq_pmul2r bp) -(leq_add2r 1) -B' - B (leq_pmul2r ap) cp.
have cp2:=(ltnW cp).
have cp1: v' <= v.
  by rewrite - (leq_pmul2r bp)-(leq_add2r 1) -B -B' (leq_pmul2r ap).
move /eqP: B; rewrite -(subnK cp1) -(subnK cp2) !mulnDl - addnA -B'.
rewrite eqn_add2r; set x := (u - u'); set y := (v - v') => /eqP eq3.
have cap: coprime b a by rewrite coprime_sym; apply:(coprime_if_bezout B').
have eq4: x = (x %/ b) * b.
  symmetry; apply /eqP; rewrite - (dvdn_eq b x).
  by move:(Gauss_dvdr x cap); rewrite mulnC eq3 {1}/dvdn modnMl eqxx => <-.
case: (posnP u') =>uz; first by move/eqP: B'; rewrite uz addn1.
have: u < b + u' by  apply: (leq_ltn_trans vb); rewrite ltn_paddr.
rewrite -(subnK cp2) -/x eq4 ltn_add2r -{3}(mul1n b) ltn_pmul2r // ltnS leqn0.
by move => /eqP qp; move: (ltn_eqF cp); rewrite -(subnK cp2) -/x eq4 qp eqxx.
Qed.

Lemma totient_ltn n: 1 < n -> totient n < n.
Proof.
move => l1n; rewrite totient_count_coprime.
rewrite -{1 3}(prednK (ltnW l1n)) big_nat_recl // /coprime gcdn0 (gtn_eqF l1n).
move:(sum_nat_const_nat 0 n.-1 1); rewrite subn0 muln1 => {2} <-.
by rewrite ltnS; apply: leq_sum => // i _; case: eqP.
Qed.

Lemma totient_prime n: prime n = (0 < n) && (totient n == n.-1).
Proof.
case: (posnP n) => np /=; first by rewrite np.
case pn:(prime n); first by rewrite -{1}(expn1 n) totient_pfactor // muln1 eqxx.
case/primePn: (negbT pn).
  by rewrite ltnS leqn1; case/orP => /eqP => h; move: np; rewrite h.
move => [d /andP[l1d ldn] /gcdn_idPr gnd].
symmetry; apply: ltn_eqF. 
have ns:= prednK np; have dc:= (prednK(ltnW l1d)).
have df: d.-1 < n.-1 by rewrite -ltnS dc ns. 
rewrite totient_count_coprime -{1}ns big_nat_recl // {1} /coprime gcdn0.
rewrite (gtn_eqF (ltn_trans l1d ldn)).
rewrite  -{2} (card_ord n.-1) - sum1_card big_mkord.
rewrite (bigD1 (Ordinal df)) // [X in _ < X] (bigD1 (Ordinal df)) //=.
rewrite dc /coprime  gnd (gtn_eqF l1d) 2!add0n add1n ltnS. 
by rewrite leq_sum // => i _; case: eqP.
Qed.

Lemma totient_pfactor_alt p e: prime p -> 0 < e -> 
    totient (p ^ e) = p ^ e - p ^ e.-1.
Proof.
move => pp ep; rewrite totient_pfactor // -{2} (prednK ep) expnS.
by rewrite - {3} (prednK (prime_gt0 pp)) mulSn addKn.
Qed.

Lemma totient_prime_alt n: 1 < n -> totient n = n.-1 -> prime n.
Proof.
move => n1; move:(ltnW n1) => n0.
move:(pdiv_prime n1); set u := (pdiv n) => pu.
move:(pfactor_coprime pu n0)(prime_gt1 pu) => [m pa pb] u1.
have lp: 0 <  logn u n by rewrite logn_gt0 mem_primes pu n0 pdiv_dvd.
have pc: coprime m (u ^ logn u n) by rewrite coprime_sym; apply:coprime_expl.
case m1: (m==1).
  set y := u.-1 * u ^ (logn u n).-1.
  have yp: 0 < y by rewrite muln_gt0 expn_gt0 -ltnS (ltnW u1) (ltn_predK u1) u1.
  rewrite pb (eqP m1) mul1n totient_pfactor// -{2 3}(prednK lp) expnS.
  rewrite - {4} (prednK (ltnW u1)) mulSn  -/y -(prednK yp) addnS /=.
  by move/eqP; rewrite - add1n eqn_add2r=> /eqP  <-; rewrite muln1.
case: (posnP m)=> mz h; first by move: n0; rewrite pb mz ltnn.
have /totient_ltn ha: 1 <m by rewrite  ltn_neqAle eq_sym m1 mz. 
have /totient_ltn hb: 1 < (u ^ logn u n). 
  by apply: (leq_trans u1); rewrite -{1} (expn1 u) leq_pexp2l // (ltnW u1). 
move: (leq_mul ha hb); rewrite mulSn mulnS addnA -(totient_coprime pc) - pb.
rewrite h addSn addSnnS (prednK n0) - {3} (add0n n) leq_add2r leqn0 addn_eq0.
by move: mz; rewrite - totient_gt0 => /gtn_eqF ->; rewrite andbF.
Qed.

(** **  Fermat of exponent two *)

Lemma gcd_aux x y (g := gcdn x y) (x' := x%/g) (y':= y%/ g):
  0 < x ->  [/\ x = x' * gcdn x y, y = y' * gcdn x y & coprime x' y'].
Proof.
move => xp.
case: (egcdnP y xp) => u v /= /eqP bz _.
move: (dvdn_gcdl x y)(dvdn_gcdr x y); rewrite !dvdn_eq => /eqP xv /eqP yv.
split =>//.  
move: bz; rewrite -[gcdn x y]mul1n -{1} yv -{1} xv !mulnA -mulnDl addnC.
by rewrite eqn_pmul2r ?gcdn_gt0 ?xp // addnC => /eqP /coprime_if_bezout.
Qed.

Lemma pythagore_aux a b c (d := (c %/ b)) :
  0 < b -> a * b^2 = c^2 -> c = d * b /\ a = d ^2.
Proof.
move => bp h; move: (esym (@dvdn_pexp2r b c 2 (ltnSn 1))).
rewrite -h {2}/dvdn modnMl dvdn_eq eqxx => /eqP h1.
by  move /eqP: h;  rewrite -{1 2} h1 expnMn eqn_pmul2r ? sqrn_gt0 // => /eqP.
Qed.


Lemma factor_square a b c (u:=a %/ gcdn a c) (v := c %/ gcdn a c):
  0 < a -> coprime a b -> a * b = c ^2 -> [/\ a = u ^2, b = v^2 & coprime u v].
Proof.
move => ap cab /eqP Eq.
move:(gcd_aux c ap); rewrite -/u -/v; move  => [av cv cuv].
move: cab; rewrite av coprime_mull => /andP [cub cgb].
move: Eq; rewrite {1}av {2} cv mulnAC expnMn - (mulnn (gcdn a c)) mulnA.
rewrite eqn_pmul2r ?gcdn_gt0 ? ap // => /eqP Eq.
move:ap; rewrite {1}av muln_gt0  => /andP [up _].
have: (u %| v ^ 2 * gcdn a c) by rewrite -Eq /dvdn modnMr.
have: (gcdn a c %| b * u ) by rewrite mulnC Eq /dvdn mulnC modnMr.
rewrite !Gauss_dvdr ? coprime_expr // => dvd1 dvd2.
move: (eqn_dvd (gcdn a c) u); rewrite dvd1 dvd2 /= => /eqP gv.
by move /eqP:Eq; rewrite gv mulnn mulnC eqn_pmul2r // => /eqP ->.
Qed.


(* not much simpler
Lemma double_square_square m n: (n ^2).*2 = m ^2 -> n = 0.
Proof.
move/eqP => h.
elim: m {-2} m (leqnn m) n h.
  move => m; rewrite leqn0 => /eqP -> n; rewrite double_eq0 expn_eq0 andbT.
  by move/eqP.
move => k IH m; rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move => /eqP -> n; case: (odd_dichot k.+1) => od h.
  by move:(f_equal odd (eqP h)); rewrite odd_exp od /= !odd_double. 
have nk: n <= k. 
  rewrite - ltnS ltn_neqAle  - leq_sqr - (eqP h) double_le1 andbT. 
  apply /negP => eq1; move: h. 
  by rewrite - (addn0 (k.+1 ^ 2)) (eqP eq1) -addnn eqn_add2l expn_eq0 //.
move: h; rewrite od - (muln2 (k.+1)./2) expnMn -[2^2]/(2 * 2) mulnA muln2 muln2.
rewrite eqn_double eq_sym => ea.
by move: od; rewrite (IH n nk k.+1./2 ea). 
Qed.

*)

Lemma double_square n: n.*2 ^2 = (n ^2) .*2 .*2.
Proof. by  rewrite -muln2 expnMn -[2^2]/(2 * 2) mulnA 2!muln2.  Qed.

Lemma double_square_square m n: (n ^2).*2 = m ^2 -> n = 0.
Proof.
move/eqP.
elim: n {-2} n (leqnn n) m; first by move => n; rewrite leqn0 => /eqP.
move => k IH n; rewrite leq_eqVlt; case/orP=> [/eqP -> m Hm |Hm]; last first.
  by apply: IH; rewrite -ltnS. 
move:(odd_double (k.+1 ^ 2)); rewrite (eqP Hm) odd_sqr => /evenE mv.
move: Hm; rewrite mv double_square eqn_double eq_sym => ea.
case: (ltnP k (m./2)).
  by rewrite - leq_sqr - leq_double (eqP ea) leqNgt double_le3.
by move => la; move: (ea); rewrite (IH  _ la _ ea) (eqn_sqr 0).
Qed.

Lemma gcd_n2 n: gcdn n 2 = if (odd n) then 1 else 2.
Proof.
by rewrite -{1} (odd_double_half n) -muln2 addnC gcdnC gcdnMDl; case: odd.
Qed.

Lemma square_odd_mod4 n: odd n -> n^2 = 1 %[mod 4]. 
Proof.
rewrite -{2} (odd_double_half n) sqrnD => ->.
by rewrite mul1n -mul2n mulnA expnMn -addnA -mulnDr addnC mulnC modnMDl.
Qed.


Lemma coprime_sqr m n: coprime (m ^2) (n ^ 2) = coprime m n.
Proof. rewrite coprime_pexpr // coprime_pexpl //. Qed.

Lemma coprimeDl m n: coprime m (m + n) = coprime m n.
Proof. by rewrite/coprime gcdnDl. Qed.

Lemma coprimeDr m n: coprime m (n + m) = coprime m n.
Proof. by rewrite/coprime gcdnDr. Qed.

Lemma pythagore_tripleA p q r 
  (x := r* (p^2 - q^2)) (y := r*(p*q).*2) (z:= r*(p^2 + q ^2)): 
  q <= p -> x^2 + y^2 = z ^2.
Proof.
rewrite /x /y/z -leq_sqr /= !expnMn -mulnDr -mul2n !expnMn => h.
rewrite -(sqrnD_sub h) subnK //; apply:nat_AGM2.
Qed.

Lemma pythagore_gcd p q:  q <= p -> coprime p q ->  odd p != odd q ->
  coprime (p ^ 2 - q ^ 2) (p * q).*2.
Proof.
move => lqp; rewrite {2}/coprime.
rewrite subn_sqr -{1 2 4 5} (subnK lqp); set r := p - q.
rewrite /coprime_sym /coprime gcdnC gcdnDr -/(coprime _ _) => cqr.
rewrite odd_add negb_eqb - addbA addbb addbF => or.
have cpq: (coprime (r * (r + q + q)) q).
  by rewrite coprime_sym /coprime Gauss_gcdr // !gcdnDr.
have cp2: coprime (r * (r + q + q)) 2.
  by rewrite /coprime gcd_n2 odd_mul - addnA odd_add or addnn odd_double.
rewrite - mul2n Gauss_gcdr // Gauss_gcdl // gcdnC Gauss_gcdl.
  by rewrite gcdnC -/(coprime _ _) coprimeDl coprime_sym.
by rewrite coprimeDl coprime_sym  coprimeDr.
Qed.

Lemma pythagore_mod4 x y z: coprime x y -> x ^ 2 + y ^ 2 = z ^ 2 ->
  odd x != odd y.
Proof.
move => cpa eq1.
case ox: (odd x); case oy: (odd y) => //.
  move:(f_equal (fun z => z %% 4) eq1); rewrite -(modnDm) square_odd_mod4 //. 
  rewrite square_odd_mod4  // (@modn_small 1) // (@modn_small 2) //.
  case oz: (odd z); first by rewrite square_odd_mod4.
  by rewrite (evenE oz) -mul2n expnMn modnMr.
move: cpa; rewrite (evenE ox) (evenE oy) -!muln2 /coprime.
by rewrite -muln_gcdl muln_eq1 andbF.
Qed.

Lemma pythagore_tripleB x y z (r := gcdn x y): x^2 + y ^2 = z^2 ->
  [\/ x=0 /\ y = z, y = 0 /\ x = z |
  exists p q, [/\ 0 < r, q < p, coprime p q, odd p != odd q &
     [/\ x = r* (p^2 - q^2), y = r*(p*q).*2 & z = r*(p^2 + q ^2) ] \/
     [/\ y = r* (p^2 - q^2), x = r*(p*q).*2 & z = r*(p^2 + q ^2) ]]].
Proof. 
case: (posnP x) => xp.
  by move /eqP; rewrite xp add0n eqn_sqr => /eqP ->; constructor 1.
case: (posnP y) => yp.
  by move /eqP; rewrite yp addn0 eqn_sqr => /eqP ->; constructor 2.
move => h;constructor 3.
case:(gcd_aux y xp); set a := _ %/ _; set b := _%/ _;  rewrite -/r => xv yv cp1.
have rp: 0 < r by rewrite gcdn_gt0 xp.
move: h xp yp; rewrite xv yv !expnMn - mulnDl {xv yv}.
move/(pythagore_aux rp); set c := z%/r; move => [-> h].
case az: (a==0); first by rewrite (eqP az) mul0n.
case bz: (b==0); first by rewrite (eqP bz) mul0n.
move => _ _; rewrite (mulnC a)  (mulnC b) (mulnC c).
wlog: a b az bz h cp1 / odd a && ~~(odd b).
  move => H; move: (pythagore_mod4 cp1 h).
  case oa: (odd a); first by move =>  /= ob; apply: H => //; rewrite oa ob.
  rewrite negb_eqb /= => /= ob; rewrite addnC in h; rewrite coprime_sym in cp1.
  have oc:odd b && ~~ odd a by rewrite oa ob.
  move:(H b a bz az h cp1 oc) =>[p [q [ha hb hc hd he]]];exists p,q.
  by split =>//;case: he => hh;[right| left].
move => /andP[oa eb].
have lac: a < c by rewrite - ltn_sqr -h ltn_paddr // expn_gt0 lt0n bz.
have lac' := ltnW lac.
move: (f_equal odd h); rewrite odd_add ! odd_sqr oa (negbTE eb) /= => oc.
have eq2:=(evenE (negbTE eb)).
have eq3: b^2 = (c-a)* (c+a) by rewrite - subn_sqr -h addKn.
move:(odd_double_half (c +a)); rewrite odd_add oa - oc add0n => eq4.
move:(odd_double_half (c -a)); rewrite odd_sub // oa - oc add0n => eq5.
have eq6: (b./2) ^2 = (c - a)./2 * (c + a)./2.
  apply/eqP; rewrite -(@eqn_pmul2l (2 * 2)) // mulnACA !mul2n eq4 eq5 - eq3.
  by rewrite  -(expnMn 2 _ 2) mul2n - eq2.
have ap: 0 < a by rewrite lt0n az.
have cp:=(ltn_trans ap lac).
have cap: coprime c a.
  by rewrite -coprime_sqr -h coprime_sym coprimeDl  coprime_sqr.
case: (posnP (c - a)./2) => lt1.
  by move /eqP:eq6; rewrite lt1 expn_eq0 - double_eq0 -eq2 bz.
have av: ((c + a)./2 - (c - a)./2) == a.
  by rewrite -eqn_double doubleB eq4 eq5 addnC -addnn -addnBA ?subKn// leq_subr.
have cv: ((c - a)./2 + (c + a)./2) == c.
  by rewrite - eqn_double doubleD eq4 eq5 (addnC c) addnA (subnK lac') addnn.
have lt2:= (leq_ltn_trans (leq_subr a c) (ltn_paddr c ap)).
have cp2: (coprime (c - a)./2 (c + a)./2).
  move: (esym oc); rewrite -coprimen2 => hw.
  rewrite /coprime -gcdnDl (eqP cv) gcdnC -(Gauss_gcdr _ hw) mul2n eq5.
  by rewrite gcdnC -{2}(subnK lac') gcdnDl gcdnC - gcdnDr subnK // gcdnC.
case: (factor_square lt1 cp2 (esym eq6)).
set q := _ %/ _; set p := _ %/ _ => eq7 eq8 cpxy.
have H w: odd w = odd (w ^2) by rewrite odd_mul andbb.
have eq9: b = (p * q).*2.  
  apply /eqP; rewrite -eqn_sqr - muln2 2!expnMn -eq8 -eq7 (mulnC (_ ./2)) -eq6.
  by rewrite - expnMn muln2 -eq2.
exists p, q; rewrite - eq9 coprime_sym; split => //.
+ by rewrite - ltn_sqr -eq7 -eq8 - ltn_double eq4 eq5.
+ by rewrite  (H p) (H q) negb_eqb -odd_add -eq7 -eq8 addnC (eqP cv).
+ by left; rewrite -eq7 - eq8 (eqP av) addnC  (eqP cv) eq9.
Qed.

Lemma Fermat4 x y z : x^2 + y^4 = z^4 -> (x == 0) || (y == 0).
Proof.
case: (posnP x) => xp //.
case: (posnP y) => yp //=.
case:(gcd_aux z yp); set a := _ %/ _; set b := _ %/ _; set r := gcdn y z. 
move => sa sb cp eqa.
move: (subn_sqr (z^2) (y^2)); rewrite -!expnM - eqa addnK sa sb.
rewrite !expnMn - mulnDl -mulnBl mulnACA mulnn => eqb.
have rp: 0 < r by rewrite gcdn_gt0  yp.
have: (r^2)^2 %| x ^2 by rewrite eqb /dvdn modnMl.
rewrite dvdn_pexp2r // => /dvdnP [c xv].
move /eqP: eqb; rewrite xv expnMn eqn_pmul2r ?expn_gt0 ? rp// => eqc.
have ap: 0 < a by move: yp; rewrite sa muln_gt0 rp andbT.
have: a < b. 
  rewrite -ltn_sqr ltnNge /leq; apply/eqP => h. 
  by move: xp; rewrite -ltn_sqr xv expnMn (eqP eqc) h.
move: (leqnn b) cp eqc ap; clear; elim: b {-2} b a c.
  by move => b a c; rewrite leqn0 => /eqP ->; rewrite ltn0.
move => K IH b a c ns cab eqa ap lab.
have ha: a ^ 2 <= b ^ 2 by rewrite leq_sqr (ltnW lab).
have eqd: c^2 + (a^2)^2 = (b^2)^2.
   by rewrite (eqP eqa) - subn_sqr subnK // leq_sqr. 
case: (posnP c) => cp; first by move/eqP:eqd;rewrite cp 2!eqn_sqr (ltn_eqF lab).
move: (cab). 
rewrite - 2!coprime_sqr -eqd addnC coprimeDl coprime_sym coprime_sqr => cac.
case oa: (odd a).
  case: (pythagore_tripleB eqd).
  + by case => /eqP; rewrite (gtn_eqF cp).
  + by case => /eqP; rewrite expn_eq0 andbT (gtn_eqF ap).
  + move => [p [q []]]; rewrite (eqP cac) ! mul1n => _ sb sc sd [][qa qb qc].
      by move: (f_equal odd qb); rewrite odd_sqr odd_double oa.
    case:(posnP q) => qp; first by move: cp; rewrite qb qp !muln0.
    have lpk: p <= K.  
       rewrite -ltnS; apply: leq_trans ns. 
       by rewrite -ltn_sqr qc ltn_paddr // expn_gt0 qp. 
    by apply: (IH p q (a*b)) => //; rewrite 1? coprime_sym // -qa -qc expnMn.
case ob: (odd b); last first.
  move: cab;rewrite (evenE oa) (evenE ob) -!muln2. 
  by rewrite /coprime -muln_gcdl muln_eq1 andbF. 
have cp2: coprime (b ^ 2 - a ^ 2)  (b ^ 2 + a ^ 2).
  have cp1:coprime (b ^ 2 + a ^ 2) 2.
    by rewrite coprimen2 odd_add !odd_sqr oa addbF.
  rewrite /coprime gcdnC -gcdnDl -addnA subnKC // addnn -muln2 Gauss_gcdl //.
  by rewrite gcdnC gcdnDl gcdnC -/(coprime _ _) coprime_sqr. 
move /eqP: (eqa); move/esym => eqa'.
case: (posnP (b ^ 2 - a ^ 2)) => dp.
  by move: cp; rewrite -sqrn_gt0 - eqa' dp. 
case: (factor_square dp cp2 eqa'); set t := _ %/ _; set s := _ %/ _.
move => t2 s2 cst.
have os: odd s by rewrite -odd_sqr -s2 odd_add !odd_sqr oa ob.
have ot: odd t by rewrite -odd_sqr -t2 odd_sub // !odd_sqr oa ob.
move: (oddE os) (oddE ot) => sv1 tv1.
set u := (s+t)./2; set v := (s-t)./2.
have cp0: t < s.
  have qa: b ^ 2 - a ^ 2  <= b^2 by rewrite leq_subr.
  have qb: b ^ 2  < b ^ 2 + a ^ 2 by apply: ltn_paddr; rewrite expn_gt0 ap.
  by move: (leq_ltn_trans qa qb); rewrite t2 s2 ltn_sqr.
have cp1: t./2 <= s./2 by apply: half_leq; apply:ltnW.
have uE: u = s./2 + t./2 +1. 
  by rewrite /u {1} sv1 {1}tv1 addSnnS -doubleS -doubleD doubleK addn1 addnS.
have vE: v =  s./2 - t./2.
  by rewrite /v {1} sv1 {1} tv1 subSS -doubleB doubleK.
have sE: s = u + v. 
  by rewrite uE vE addnAC -2!addnA (addnA t./2) subnKC //addnA addnn addn1. 
have tE: t = u - v. 
  by rewrite uE vE (subnBA _ cp1) (addnAC s./2) -2!addnA addnn add1n -tv1 addKn.
have luv: v < u by rewrite uE addn1 ltnS vE leq_BD.
have cuv: coprime u v. 
  move: cst; rewrite sE tE /coprime gcdnC -gcdnDl -addnA (subnKC (ltnW luv)).
  by rewrite addnn - muln2 Gauss_gcdl ? coprimen2 -?sE // sE gcdnC gcdnDl.
have suv: u^2 + v ^2 = b^2.
  have h: (b^2).*2 = s^2 + t ^2 by rewrite -t2 -s2 -addnA (subnKC ha) addnn.
  apply/eqP; rewrite - eqn_double h sE tE sqrnD (sqrn_sub (ltnW luv)) -addnA.
  by rewrite subnKC ?addnn // nat_Cauchy.
have puv: v * (2 * u) = a ^2.
  by move/eqP:(sqrnD u v);rewrite suv -sE -s2 eqn_add2l mulnA mulnC => /eqP ->.
case: (posnP v) => vz; first by move: ap; rewrite - sqrn_gt0 -puv vz.
case: (posnP u) => uz; first  by move: luv; rewrite uz ltn0.
case:(pythagore_tripleB suv).
    by move => []; rewrite uE addn1.
  by move => [vzz]; move: vz; rewrite vzz.
move => [p [q [gp lqp cpq opq]]]; rewrite (eqP cuv) ! mul1n.
have odf: odd (p ^ 2 - q ^ 2).
  by rewrite odd_sub ?odd_sqr ?leq_sqr ?(ltnW lqp) //= - negb_eqb.
have pp: 0 < p by  move: lqp; case p. 
have Hw w: 0 < w -> w <= w^2 by move => h; rewrite -{1}(expn1 w) leq_pexp2l.
case=> [] [up vp bp].
  case: (posnP q) => qp; first by move: vz; rewrite vp qp !muln0.
  have cp3: coprime u (2* v).
     by rewrite /coprime Gauss_gcdl //  -/(coprime _ _) coprimen2 up. 
  have puv': u * (2 * v) = a ^ 2 by rewrite - puv mulnCA mulnA mulnC.
  case:(factor_square uz cp3 puv'); set d := _ %/ _; set e := _ %/_.
  move => us vs cp4.
  move: (f_equal odd vs); rewrite odd_sqr mul2n odd_double => oe.
  move /eqP: vs; rewrite  (evenE (esym oe)) - mul2n expnMn.
  rewrite vp - mulnA !mul2n 2! eqn_double => pqs.
  case: (factor_square pp cpq (eqP pqs)).
  set aa := _ %/ _; set bb := _ %/ _ => [Ha Hb Hc].
  have bbp: 0  < bb by rewrite -sqrn_gt0 -Hb.
  have cba: bb < aa by rewrite -ltn_sqr -Ha -Hb.
  case: (posnP aa) => aap; first by move: cba; rewrite aap;case: (aa).
  have aaK: aa <= K. 
     move: (Hw aa aap); rewrite -Ha => hb; apply: (leq_trans hb).
     rewrite -ltnS; apply: leq_trans ns. 
     by apply:(leq_ltn_trans (Hw p pp)); rewrite bp ltn_paddr // sqrn_gt0.
  rewrite coprime_sym in Hc.
  by apply: (IH aa bb d aaK Hc) => //; rewrite -Ha -Hb -us up -subn_sqr.
have cp3 : coprime v (2* u). 
  by rewrite /coprime Gauss_gcdl 1? coprime_sym // -/(coprime _ _) coprimen2 up.
case:(factor_square vz cp3 puv); set d:= _ %/ _; set e := _ %/ _  => us vs cp4.
move: (f_equal odd vs); rewrite odd_sqr mul2n odd_double => oe.
move /eqP: vs; rewrite (evenE (esym oe)) - mul2n expnMn -[2^2]/(2*2) - mulnA.
rewrite vp !mul2n !eqn_double => pqs.
case: (posnP q) => qp; first by move: uz; rewrite vp qp !muln0.
case: (factor_square pp cpq (eqP pqs)).
set aa := _ %/ _; set bb := _ %/ _ => [Ha Hb Hc].
have bbp: 0 < bb by rewrite -sqrn_gt0 -Hb.
have cba: bb < aa by rewrite -ltn_sqr -Ha -Hb.
case: (posnP aa) => aap; first by move: cba; rewrite aap;case: (aa).
have aaK: aa <= K. 
   move: (Hw aa aap); rewrite -Ha => hb; apply: (leq_trans hb).
   rewrite -ltnS; apply: leq_trans ns. 
   by apply:(leq_ltn_trans (Hw p pp)); rewrite bp ltn_paddr // sqrn_gt0.
rewrite coprime_sym in Hc.
by apply: (IH aa bb d aaK Hc) => //; rewrite -Ha -Hb -us up -subn_sqr.
Qed.

Lemma Fermat4_alt x y z (pa:= fun x => exists y, x= y^2 \/ x = (y^2).*2)
  (pb := fun x y z => [\/ pa x /\ pa y, pa y /\ pa z | pa z /\ pa x]):
  x^2 + y ^2 = z ^2 -> coprime x y -> pb x y z -> (x == 0) || (y == 0).
Proof.
elim: z {-2} z (leqnn z) x y.
   move => z; rewrite leqn0 => /eqP -> x y /eqP; rewrite addn_eq0 expn_eq0 //.
   by rewrite andbT; move/andP => [->].
move => K Hrec z zB x y ha hb hc.
wlog: x y ha hb hc /(odd y).
  move => H; move:(pythagore_mod4 hb ha); case oy: (odd y).
    by move => _; apply: H.
  rewrite coprime_sym in hb; rewrite addnC in ha; rewrite negb_eqb addbF orbC. 
  apply: H => //; case: hc => [][qa qb]. 
  - by constructor 1.
  - by constructor 3.
  - by constructor 2.
move => oy; case: (pythagore_tripleB ha).
    by move => [->].
  by move => [->]; rewrite orbT.
move => [p [q []]]; rewrite (eqP  hb) !mul1n => _ lqp cp2 opq.
case => [][yv xv zv]; first by move: oy; rewrite xv odd_double.
have oz: odd z by rewrite -odd_sqr - ha odd_add !odd_sqr oy xv odd_double.
have paw w:  pa w -> odd w ->exists y', w = y'^2.
  move => [t]; case => ->; [ by exists t | by rewrite odd_double].
have lb: (q ^ 2) <= (p ^ 2)  by rewrite leq_sqr (ltnW lqp).
have la: (q ^ 2) ^ 2 <= (p ^ 2) ^ 2 by rewrite leq_sqr.
have zz: z = 0 -> (x == 0) || (y == 0).
  by move => h; move /eqP:ha; rewrite h addn_eq0 !expn_eq0 !andbT => /andP[->].
case (posnP q) => qp; first by rewrite xv qp !muln0.
case (posnP p) => pp; first by rewrite xv pp. 
have pax: pa x -> pa p /\ pa q.
  rewrite xv; move: opq cp2; rewrite negb_eqb; clear;wlog: p q /odd p.
      move => H; case op: (odd p) => ww; first by apply:H => //; rewrite op.
      rewrite coprime_sym mulnC=> sa sb.
      simpl in ww; have opq: odd q (+) odd p by rewrite ww op.
      by case: (H q p ww opq sa sb).
   case: (posnP p) => pp; first by rewrite pp.
   move => op; rewrite op /= => oq cpq [t]; case.
     rewrite - muln2 -mulnA (mulnC q) => eqa.
     have cp': coprime p (2 * q) by rewrite /coprime Gauss_gcdr // coprimen2.
     case: (factor_square pp cp' eqa); set u:= _ %/ _; set v := _ %/ _.
     move => -> hb hc.
     move:(f_equal odd (esym hb)); rewrite odd_sqr mul2n odd_double => ov.
     split; first by exists u; left.
     move /eqP: hb; rewrite (evenE ov) - mul2n expnMn - (mulnA 2 2) !mul2n => h.
     by exists (v./2); right; apply/eqP; rewrite -eqn_double h. 
  move/eqP; rewrite eqn_double => /eqP eqa.
  case: (factor_square pp cpq eqa); set u := _ %/ _; set v := _ %/ _.
  move => -> -> cp;split; [ by exists u; left | by exists v; left].
have lpk: p^2 <= K. 
  by rewrite -ltnS; apply: leq_trans zB; rewrite zv ltn_paddr // sqrn_gt0.
have lpk1: p <= K.
  by apply: leq_trans lpk; rewrite -{1}(expn1 p) leq_pexp2l.
case: hc => [] [he hf].
+ move: (paw _ hf oy) => [y' y'v].
  move: (pax he)=> [sa sb].
  have eq2: q ^ 2 + y' ^ 2 = p ^ 2 by rewrite -y'v yv subnKC.
  have cp3: coprime q y'.
    by rewrite -coprime_sqr -coprimeDl eq2 coprime_sqr coprime_sym.
  have rc: pb q y' p by constructor 3.
  move: (Hrec p lpk1 q y' eq2 cp3 rc); rewrite  (gtn_eqF qp) /= y'v => /eqP.
  by move => ->; rewrite orbT.
+ move: (paw _ he oy) => [y' ysv]; move: (paw _ hf oz) => [z' zsv].
  have ra:(y' * z') ^ 2 + (q ^ 2) ^ 2 = (p ^ 2) ^ 2.
    by rewrite expnMn - ysv - zsv yv zv - subn_sqr subnK.
  have rb:coprime (y' * z') (q ^ 2). 
    by rewrite -coprime_sqr coprime_sym - coprimeDr ra !coprime_sqr coprime_sym.
  have rc:pb (y' * z') (q ^ 2) (p ^ 2). 
    constructor 2; split; [ by exists q; left |  by exists p; left].
  move: (Hrec (p^2) lpk (y'*z') (q^2) ra rb rc). 
  rewrite expn_eq0  (gtn_eqF qp) muln_eq0 orbF; case/orP => /eqP hw.
    by rewrite ysv hw orbT.
    by apply:zz; rewrite zsv hw.
+ move: (paw _ he oz) => [z' z'v].
  move: (pax hf)=> [sa sb].
  have eq2: p ^ 2 + q ^ 2 = z' ^ 2 by rewrite - z'v zv.
  have pbb: pb p q z' by constructor 1.
  have lt1: z' <= K.
    move: (qp)(pp); rewrite - sqrn_gt0 - (sqrn_gt0 p) => l1 l2.
    move:(leq_add l2 l1) zB; rewrite - zv z'v; clear; case z' => //; case=> //.
    move => n nb nc; rewrite - ltnS; apply: leq_trans nc.
    by rewrite - mulnn; apply:ltn_Pmull.
  by move: (Hrec z' lt1 p q eq2 cp2 pbb); rewrite (gtn_eqF qp) (gtn_eqF pp).
Qed.

Lemma Fermat4' x y z : x^2 + y^4 = z^4 -> (x == 0) || (y == 0).
Proof.
case: (posnP x) => xp //.
case: (posnP y) => yp //=.
case:(gcd_aux z yp); set a := _ %/ _; set b := _ %/ _; set r:= gcdn y z. 
move => sa sb cp eqa.
move: (subn_sqr (z^2) (y^2)); rewrite - !expnM - eqa addnK sa sb.
rewrite !expnMn - mulnDl -mulnBl mulnACA mulnn => eqb.
have rp: 0 < r by rewrite gcdn_gt0  yp.
have r4p:0 < r ^ (2 * 2) by rewrite  expn_gt0 rp.
have: (r^2)^2 %| x ^2 by rewrite eqb /dvdn modnMl.
rewrite dvdn_pexp2r // => /dvdnP [c xv].
move /eqP: eqa; rewrite sa sb xv !expnMn mulnn - expnM -mulnDl eqn_pmul2r //.
rewrite -[4]/(2*2) 2!expnM => /eqP eqc.
have cpp: coprime c (a^2).
  by rewrite -coprime_sqr coprime_sym -coprimeDr eqc !coprime_sqr.
move: (Fermat4_alt eqc cpp); set W:= (or3 _ _ _) => H.
have wt: W by constructor 2; split; [ exists a| exists b]; left.
move: (H wt); case/orP => ea.
  by move: xp; rewrite xv (eqP ea).
by move: ea yp; rewrite expn_eq0 andbT sa => /eqP ->.
Qed.


Lemma Fermat2_bound a b c: a^2 + b^2 = c^2 -> b <= c ?= iff (a == 0).
Proof.
move => h. 
by rewrite - (mono_leqif leq_sqr) - h - {1} (add0n (b^2))
             (mono_leqif (leq_add2r (b^2))) -[0]/(0^2) (mono_leqif leq_sqr). 
Qed.

Lemma Fermat2_bound2 a b c: a^2 + b^2 = c^2 -> c <= (a+b) ?= iff (a*b == 0).
Proof.
move => h. 
rewrite - (mono_leqif leq_sqr) sqrnD - h - {1} (addn0 (a^2 + b^2)).
by rewrite (mono_leqif (leq_add2l (a^2 + b^2))); split => //; case: (a*b).
Qed.


Lemma square_plus1_square m n: n ^2 + 1 = m ^2 -> n = 0.
Proof.
rewrite -{2}[1]/(1^2) => h; apply/eqP.
case:(Fermat2_bound2 h);rewrite muln1 addn1 leq_eqVlt ltnS; case: eqP => //= _. 
by rewrite addnC in h; case:(Fermat2_bound h); rewrite  eqn_leq => -> /= ->.
Qed. 


Lemma square_plus1_square_alt m n: n ^2 + 1 = m ^2 -> n = 0.
Proof.
move => h.
case: (ltnP n m); rewrite -leq_sqr -h addn1 ? ltnn//.
rewrite - addn1 sqrnD addnAC addn1 ltnS  muln1 - {2} (addn0 (n^2)).
by rewrite leq_add2l leqn0 muln_eq0 /= => /eqP.
Qed.

Lemma square_plus2_square m n: n ^2 + 2 = m ^2 -> False.
Proof.
move => eq1.
case: (ltnP n m);rewrite -leq_sqr -eq1; last by rewrite leqNgt ltn_paddr.
rewrite -addn1 sqrnD -addnA leq_add2l muln1 mul2n add1n (ltn_double n 1).
by move: eq1; case: n => //=; rewrite add0n; move/(@double_square_square m 1).
Qed.


Lemma square_plus3_square m n: n ^2 + 3 = m ^2 -> (n = 1 /\ m = 2). 
Proof.
move => eq1.  move:(subn_sqr m n); rewrite -eq1 addKn.
case: (ltnP m n); first by rewrite -ltn_sqr - (addn0 (n^2)) -eq1 ltn_add2l.
move => ha; rewrite -{2 3} (subnK ha)- addnA addnn => eqB.
have: (m-n) < 2 by rewrite - ltn_sqr ltnS eqB mulnDr mulnn leq_addr.
move: eqB;case: (m-n) => //; case => // /eqP.
by rewrite mul1n -[3]/(1+1.*2) (eqn_add2l) eqn_double => /eqP <-.
Qed.

Lemma square_plus4_square m n: n ^2 + 4 = m ^2 -> n = 0.
Proof.
move => h; move:(subn_sqr m n); rewrite - h addKn.
case: (ltnP m n); first by rewrite -ltn_sqr - (addn0 (n^2)) -h ltn_add2l.
move => ha; rewrite -{2} (subnK ha)- addnA addnn.
rewrite -(odd_double_half (m-n)); case: odd.
  by move => eqA; move:(f_equal odd eqA); rewrite odd_mul !odd_add !odd_double.
move/esym; move/eqP; rewrite -[4]/(1.*2.*2) add0n -doubleD -doubleMr.
by rewrite -doubleMl 2!eqn_double muln_eq1 => /andP[/eqP -> /eqP]; case.
Qed.



Fact square_plus4_square_alt m n: n ^2 + 2^2 = m ^2 -> n = 0.
Proof.
have: prime 2 by []; move/primeP => [_ dvd2]. 
case /pythagore_tripleB; [ by case => h | by case | ].
move => [p [q [ha hb hc hd]]]; case; case => ea eb ec.
   move/eqP: eb;rewrite {2} ea -doubleMr (eqn_double 1) eq_sym !muln_eq1. 
   by move => /and3P [ /eqP -> /eqP ->  /eqP  -> ]. 
rewrite subn_sqr in ea.
have he: (p + q) %| 2 by rewrite ea mulnA /dvdn modnMl.
case/orP:  (dvd2 _ he) => /eqP.
   move: eb; clear; case: q; first by rewrite !muln0. 
   move => q av /eqP; rewrite addnS eqSS addn_eq0 => /andP [ha hb].
   by rewrite av (eqP ha) muln0.
by move/(f_equal odd); rewrite odd_add -negb_eqb hd.
Qed.


Lemma square_plus4_square_alt2 m n: n ^2 + 4 = m ^2 -> n = 0.
Proof.
rewrite -[4]/(2^2) => h; apply/eqP.
case:(Fermat2_bound2 h). rewrite muln2 addn2 double_eq0 2!leq_eqVlt 2!ltnS.
rewrite addnC in h; move/leqifP:(Fermat2_bound h) => /= lnm.
rewrite leqNgt lnm /=; case/orP; first by move->.
rewrite orbF eqSS => /eqP k; move:(congr1 odd h). 
by rewrite k odd_add !odd_sqr/=; case: odd.
Qed.

Lemma square_plus9_square n m: n ^2 + 3^2 = m ^2 -> (n = 0 \/ n = 4).
Proof.
case /pythagore_tripleB; [ by case => h _; left | by case | ].
move => [p [q[ha hb hc hd]]] [] [ea eb _].
  by move: (f_equal odd eb); rewrite -doubleMr odd_double.
rewrite subn_sqr in ea.
have /primeP [_ h]: prime 3 by [].
have da: (p + q) %| 3 by rewrite ea mulnA /dvdn modnMl.
case/orP:  (h _ da) => /eqP rv.
   move: eb hb rv; clear; case: q; first by rewrite !muln0 => ->; left.
   move => q _ np => /eqP; rewrite addnS eqSS addn_eq0 => /andP [ha hb].
   by move: np; rewrite (eqP ha) (eqP hb).
move/eqP: ea; rewrite rv mulnA -{1}[3]/(1*3) eqn_pmul2r // eq_sym muln_eq1.
move /andP => [r1 pq].
right; move /eqP: rv;rewrite eb (eqP r1) -(subnK (ltnW hb)) (eqP pq).
by rewrite -addnA eqSS addnn (eqn_double q 1) => /eqP ->.
Qed.

Lemma square_plus16_square n m: 
  (n ^2 + 4^2 == m ^2) = (n==0) && (m==4)||(n==3)&&(m==5).
Proof.
apply/idP/orP; last by case => /andP [/eqP -> /eqP ->] //.
case:(ltnP n m); last first. 
  move => cap; have /gtn_eqF -> //: m^2 < n ^ 2 + 4^2.
  by apply: (@leq_ltn_trans (n^2)); rewrite ? leq_sqr // -addSnnS leq_addr.
move => lnm /eqP h; move: lnm; rewrite leq_eqVlt; case/orP => lmn.
  by move:(congr1 odd h); rewrite -(eqP lmn) odd_add !odd_sqr /=; case: odd. 
move:lmn; rewrite -(leq_sqr) - addn2 -h sqrnD - addnA leq_add2l.
rewrite - [4 ^ 2]/( 2 ^ 2  + 4 * 3) leq_add2l (mulnC n) mulnA leq_pmul2l //.
rewrite leq_eqVlt; case/orP => n3; [right | left].
  by move/eqP: h; rewrite (eqP n3) (eqn_sqr 5) eq_sym.
case: (Fermat2_bound h); rewrite leq_eqVlt eq_sym -leq_sqr -h.
by rewrite -[5^2]/(3^2+4^2) leq_add2r leq_sqr -ltnS ltnNge n3 orbF => -> <-. 
Qed.


Fact square_plus16_square_alt n m: (n ^2 + 4^2 = m ^2) -> n = 0 \/ n = 3.
Proof.
case /pythagore_tripleB; [ by case => h _; left | by case | ].
have H1 a b:  2 == a * b -> (a==1) || (a == 2).
  by case: a => [|[|[| a]]] => //; rewrite mulnC;case: b.
have H a b:  odd b -> 2 == a * b -> (a == 2).
  move => ob h; case/orP: (H1 _ _ h);last by move => ->. 
  by move => /eqP a1; move:(f_equal odd (eqP h)); rewrite a1 mul1n ob.
move => [p [q[ha hb hc hd]]]; case; case => ea eb ec.
  move/eqP: eb; rewrite -{1}[4]/(2.*2) -doubleMr eqn_double => ed.
  case opq: (odd (p * q)). 
     move: opq hd; rewrite odd_mul; case: odd; case: odd => //=.
  move: ed; rewrite -{1} [2]/(1.*2) (evenE opq) -doubleMr eqn_double  eq_sym.
  rewrite muln_eq1 -(eqn_double _./2) -(evenE opq) => /andP [g1 g2].
  rewrite eq_sym in g2;case/orP: (H1 _ _ g2) => /eqP pv; rewrite pv in g2.
    by rewrite mul1n in g2; move: hb; rewrite -(eqP g2) pv.
  by right;move: g2; rewrite ea (eqP g1) mul1n pv mul2n eqn_double => /eqP <-.
have hb':= (ltnW hb).
have od: odd (p^2 - q^2).
   by rewrite odd_sub ?leq_sqr // !odd_sqr  -negb_eqb.
have g4: gcdn n 4 = 4.
  move: (f_equal odd ea); rewrite odd_mul od /= andbT => /esym neg.
  move: ea;rewrite (evenE neg) -[4]/(2.*2) -doubleMl => /eqP.
  by rewrite eqn_double => h; rewrite (eqP (H _ _ od h)).
move /eqP:ea; rewrite g4 -{1} (muln1 4) eqn_pmul2l // eb => /eqP h.
have: q^2  + 1 = p ^2 by rewrite {2} h subnKC // leq_sqr.
by move/ square_plus1_square => ->; left; rewrite !muln0.
Qed.

Lemma square_plus_square_3square x y z: x^2 + y^2 = 3 * z ^2 -> z = 0.
Proof.
wlog: x y/ y <= x.
  by move => H; case/orP: (leq_total y x); [| rewrite addnC]; apply:H. 
case: (posnP x) => xp. 
  rewrite xp leqn0 => /eqP -> /eqP; rewrite eq_sym muln_eq0 expn_eq0 /=.
  by rewrite andbT => /eqP.
case (gcd_aux y xp); set a := _ %/ _; set b := _ %/ _.
move => {3} -> {3} ->.
rewrite !expnMn -mulnDl => cp _ eqa. 
case: (posnP z) => //; rewrite -sqrn_gt0 => zp.
have /(logn_Gauss ((gcdn x y) ^2)): coprime 3 (a ^ 2 + b ^ 2).
  move: (dvdn_gcd 3 a b).
  rewrite (eqP cp) /= /dvdn /coprime -gcdn_modr -modnDm - modnMm - (modnMm b).
  move: (@ltn_pmod a 3 isT); move: (@ltn_pmod b 3 isT).
  case:(a %% 3) => [|[|[]]];case:(b %% 3) => [|[|[]]] => //. 
rewrite eqa lognM // logn_prime // !lognX => H.
by move: (f_equal odd H); rewrite !mul2n add1n /= !odd_double.
Qed.



(* Functions on lists *) 
Lemma seq2_ind (T1 T2 : Type) (P : seq T1 -> seq T2 -> Prop) :
   P [::] [::] ->
   (forall x1 x2 s1 s2, P s1 s2 -> P (x1 :: s1) (x2 :: s2)) ->
   forall s1 s2, size s1 == size s2 -> P s1 s2.
Proof.
move=> Pnil Pcons; elim=> [|x1 l1 IH1]; case=> // x2 l2 /= H; auto.
Qed.

Lemma rev_inj  (T: Type) : injective (@rev T).
Proof. by apply: inv_inj; apply: revK. Qed.

Lemma all_rev (T: eqType) P (l: seq T) : all P (rev l) = all P l.
Proof. 
by apply /allP/allP => H x xi; apply:H; [rewrite mem_rev |rewrite - mem_rev].
Qed.

Lemma head_rev (T: Type) (a:T) l: head a (rev l) = last a l.
Proof.
by elim: l a => // a l H b; rewrite rev_cons - cats1 /= -H;case: rev. 
Qed.

Lemma split_rev (T: Type) (a:T) l: 
  rev (a :: l) = last a l :: behead (rev (a :: l)). 
Proof. by rewrite rev_cons {1} headI head_rev. Qed.

Lemma rem_rcons1 a b l: a < b -> rem a (rcons l b) = rcons (rem a l) b.
Proof.
move => h; elim:l => /=; first by rewrite gtn_eqF.
by move => x l H /=; case:(x==a) => //; rewrite H rcons_cons.
Qed.

Lemma rem_rcons2 (T:eqType) (a: T) l: a \notin l -> rem a (rcons l a) = l.
Proof.
elim: l => [| b l H]; rewrite /= ?eqxx //  inE /= eq_sym.
by case: (b==a) => //=; move/H => ->.
Qed.

Lemma rem_rcons2_inv (T:eqType) (a: T) l (s := take (index a l) l):
  rem a (rcons l a) = l -> a\notin s /\ l = s ++ nseq (size l - (index a l)) a.
Proof.
rewrite /s{s} => h; split.
  elim:l {h} => // b l Hr /=;case: ifP => //.
  by rewrite eq_sym in_cons negb_or Hr => ->.
elim:l h => // b l IHl /=; case: eqP.
  move => ->; rewrite subn0 cat0s; clear IHl b; elim:l => // b l Hr /= [->].
  by move/Hr ->.
by move => nba [] /IHl; rewrite subSS cat_cons => <-.
Qed.  

Definition succ_seq l :=  [seq i.+1 | i <- l].
Definition pred_seq l :=  [seq i.-1 | i <- l].

Lemma seq_prednK l: all (leq 1) l ->  l = succ_seq (pred_seq l).
Proof. 
by elim:l => // a l H /= /andP [] /prednK -> /H <-.
Qed.

Lemma iota_S a n: iota a.+1 n = succ_seq (iota a n).
Proof. by elim: n a => // k H m /=; rewrite H. Qed. 

Lemma iota_Sr i n: iota i n.+1 = rcons (iota i n)  (i+n).
Proof. by elim: n i => [i| n H i]; rewrite ? addn0 // /= - addSnnS - H. Qed.

Lemma last_iota a b c: last c (iota a b.+1) = a + b.
Proof. by rewrite iota_Sr last_rcons. Qed.

Lemma last_mkseq (T : Type) (f: nat -> T) a b c: 
  last c [seq f i | i <- iota a b.+1] = f (a + b).
Proof. by rewrite iota_Sr map_rcons last_rcons. Qed.

Lemma mkseq_succ (T: Type) (f: nat -> T) n: 
  mkseq f n.+1 = rcons (mkseq f n) (f n).
Proof.
rewrite /mkseq - {3} (add0n n).
by elim: n (0) => [n |n H m]; rewrite ? addn0 //= addnS - addSn - H.
Qed.


(** *** Copy of the std lib   *)
Fixpoint fib_rec n :=
  if n is n1.+1 then
    if n1 is n2.+1 then fib_rec n1 + fib_rec n2
    else 1
  else 0.

Definition fib := nosimpl fib_rec.

Lemma fibE : fib = fib_rec.
Proof. by []. Qed.

Lemma fib0 : fib 0 = 0.
Proof. by []. Qed.

Lemma fib1 : fib 1 = 1.
Proof. by []. Qed.

Lemma fibSS n: fib n.+2 = fib n.+1 + fib n.
Proof. by []. Qed.


Lemma fib_gt0 m: 0 < m -> 0 < fib m.
Proof. by elim: m=> [|[|m] IH _] //; rewrite fibSS addn_gt0 IH. Qed.

Lemma fib_smonotone m n: 1 < m < n -> fib m < fib n.
Proof.
elim: n=> [|[|n] IH]; first by rewrite andbF.
  by case: (ltngtP 1 m).
rewrite fibSS andbC; case/andP; rewrite leq_eqVlt; case/orP.
  by rewrite eqSS; move/eqP=> -> H1m; rewrite -addn1 leq_add2l fib_gt0.
by move=> H1m H2m; apply: ltn_addr; apply: IH; rewrite H2m.
Qed.

Lemma fib_monotone m n: m <= n -> fib m <= fib n.
Proof.
elim: n=> [|[|n] IH]; first by case: m.
  by case: m{IH}=> [|[]].
rewrite fibSS leq_eqVlt; case/orP=>[|Hm]; first by move/eqP->.
apply: (leq_trans (IH Hm)); exact: leq_addr.
Qed.

Lemma fib_eq1 n: (fib n == 1) = ((n == 1) || (n == 2)).
Proof.
case:n => [|[|[|n]]] //;case: eqP => // Hm; have: 1 < 2 < n.+3 by [].
by move/fib_smonotone; rewrite Hm.
Qed.


Lemma fib_eq m n:
  (fib m == fib n) = [|| m == n, (m == 1) && (n == 2) | (m == 2) && (n == 1)].
Proof.
wlog: m n/ m <= n=> [HH|].
  case/orP: (leq_total m n)=> Hm; first by exact: HH.
  by rewrite eq_sym HH // eq_sym ![(_ == 1) && _]andbC [(_ && _) || _] orbC.
rewrite leq_eqVlt; case/orP; first by move/eqP->; rewrite !eqxx.
case: m=> [|[|m]] Hm. 
- by rewrite (ltn_eqF (fib_gt0 Hm)) (ltn_eqF Hm).
- by rewrite eq_sym fib_eq1 orbF eq_sym. 
have: 1 < m.+2 < n by [].
move/fib_smonotone =>/ltn_eqF ->.
by case: n Hm=> [|[|n]] // /ltn_eqF -> //; rewrite andbF. 
Qed.

Lemma fib_add m n:
  m != 0 ->  fib (m + n) = fib m.-1 * fib n + fib m * fib n.+1.
Proof.
elim: m {-2}m (leqnn m) n=> [[] // _ |m IH m1].
rewrite leq_eqVlt; case/orP=> [|Hm]; last first.
  by apply: IH; rewrite -ltnS.
move/eqP->; case: m IH=> [|[|m]] IH n _.
- by rewrite mul1n.
- by rewrite add2n fibSS addnC !mul1n.
- rewrite 2!addSn fibSS -addSn !IH // addnA [fib _ * _ + _ + _]addnAC.
by rewrite -addnA -!mulnDl -!fibSS.
Qed.

Lemma fib_sub m n: n <= m ->
   fib (m - n) = if odd n then fib m.+1 * fib n - fib m * fib n.+1
                 else fib m * fib n.+1 - fib m.+1 * fib n.
Proof.
elim: m n => [|m IH]; first by case. 
case=> [|n Hn]; first by rewrite muln0 muln1 !subn0.  
by rewrite subSS IH //=;case:odd; rewrite !fibSS !mulnDr !mulnDl !subnDA !addKn.
Qed.

Lemma fib_doubleS n: fib (n.*2.+1) = fib n.+1 ^ 2 + fib n ^ 2.
Proof. by rewrite -addnn -addSn fib_add // addnC. Qed.

Theorem dvdn_fib m n: m %| n -> fib m %| fib n.
Proof.
case/dvdnP=> n1 ->.
elim: {n}n1 m=> [|m IH] // [|n]; first by rewrite muln0.
by rewrite mulSn fib_add // dvdn_add //; [apply dvdn_mull | apply dvdn_mulr].
Qed.


Lemma fib_prime p: p != 4 -> prime (fib p) -> prime p.
Proof.
move=> Dp4 Pp.
apply/primeP; split; first by case: (p) Pp  => [|[]].
move=> d; case/dvdnP=> k Hp.
case/primeP: (Pp); rewrite Hp => _ Hf.
case/orP: (Hf _ (dvdn_fib (dvdn_mulr d (dvdnn k)))).
  rewrite fib_eq1; case/orP; first by move/eqP->; rewrite mul1n eqxx orbT.
  move/eqP=> Hk.
  case/orP: (Hf _ (dvdn_fib (dvdn_mull k (dvdnn d)))).
    rewrite fib_eq1; case/orP; first by move->.
    by move/eqP=>Hd; case/negP: Dp4; rewrite Hp Hd Hk.
  rewrite fib_eq; case/or3P; first by move/eqP<-; rewrite eqxx orbT.
    by case/andP=>->.
  by rewrite Hk; case: (d)=> [|[|[|]]].
rewrite fib_eq; case/or3P; last by case/andP;move/eqP->; case: (d)=> [|[|]].
  rewrite -{1}[k]muln1; rewrite eqn_mul2l; case/orP; move/eqP=> HH.
    by move: Pp; rewrite Hp HH.
  by rewrite -HH eqxx.
by case/andP; move/eqP->; rewrite mul1n eqxx orbT.
Qed.


Lemma fib_sum n: \sum_(i < n) fib i = (fib n.+1).-1.
Proof.
elim:n => [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH fibSS; case: fib (fib_gt0 (ltn0Sn n)). 
Qed.

Lemma fib_sum_even n: \sum_(i < n) fib i.*2 = (fib n.*2.-1).-1.
Proof.
elim:n => [|n IH]; first by rewrite big_ord0.
rewrite big_ord_recr IH; case: (n)=> [|n1] //.
rewrite (fibSS (n1.*2.+1)) addnC -[(n1.+1).*2.-1]/n1.*2.+1.
by case: fib (fib_gt0 (ltn0Sn ((n1.*2)))).
Qed.

Lemma fib_sum_odd n: \sum_(i < n) fib i.*2.+1 = fib n.*2.
Proof.
elim:n=> [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr IH /= addnC -fibSS.
Qed.

Lemma fib_sum_square n: \sum_(i < n) (fib i)^2 = fib n * fib n.-1.
Proof.
elim:n=> [|n IH]; first by rewrite big_ord0.
by rewrite big_ord_recr /= IH -mulnDr addnC mulnC; case: (n). 
Qed.

Lemma bin_sum_diag n: \sum_(i < n) 'C(n.-1-i,i) = fib n.
Proof.
elim: n {-2}n (leqnn n)=> [[] // _ |n IH n1]; first by rewrite big_ord0.
rewrite leq_eqVlt; case/orP=> [|Hn]; last by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|[|n]] IH.
- by rewrite big_ord_recr big_ord0.
- by rewrite !big_ord_recr big_ord0.
rewrite fibSS -!IH // big_ord_recl bin0 big_ord_recr /= subnn bin0n addn0.
set ss := \sum_(i < _) _.
rewrite big_ord_recl bin0 -addnA -big_split; congr (_ + _).
by apply eq_bigr=> i _ /=; rewrite -binS subSn //; case: i.
Qed.

(** lucas *)

Fixpoint lucas_rec n :=
  if n is n1.+1 then
    if n1 is n2.+1 then lucas_rec n1 + lucas_rec n2
    else 1
  else 2. 

Definition lucas := nosimpl lucas_rec.

Lemma lucasE : lucas = lucas_rec.
Proof. by []. Qed.

Lemma lucas0 : lucas 0 = 2.
Proof. by []. Qed.

Lemma lucas1 : lucas 1 = 1.
Proof. by []. Qed.

Lemma lucasSS n: lucas n.+2 = lucas n.+1 + lucas n.
Proof. by []. Qed.


Lemma lucas_fib n: n != 0 -> lucas n = fib n.+1 + fib n.-1.
Proof.
elim: n {-2}n (leqnn n)=> [ [] // |n IH n1].
rewrite leq_eqVlt; case/orP=> [|Hn1]; last  by apply: IH; rewrite -ltnS.
move/eqP->; case: n IH=> [|[|n] IH _] //.
by rewrite lucasSS !IH // addnCA -addnA -fibSS addnC.
Qed.

Lemma lucas_gt0 m: 0 < lucas m.
Proof.
by elim:m=> [|[|m] IH] //; rewrite lucasSS addn_gt0 IH.
Qed.

Lemma double_lucas n: 3 <= n -> (lucas n).*2 = fib (n.+3) + fib (n-3).
Proof.
case:n => [|[|[|n]]] // _ ; rewrite !subSS subn0.
rewrite fibSS fibSS -addnA addnAC addnA addnn lucas_fib //= doubleD - addnA.
by rewrite  (addnC (fib n)) (fibSS n.+1) - addnA -fibSS addnn.
Qed.

Lemma fib_double_lucas n: fib (n.*2) = fib n * lucas n.
Proof.
case:n=> [|n]; rewrite // -addnn fib_add // lucas_fib // mulnDr addnC /=.
by rewrite (mulnC (fib n)(fib n.+1)).
Qed.

(** Stuff not in the library *)

Definition like_fib F := (forall n, F n.+2 = F n.+1 + F n).

Lemma fib_like_fib: like_fib fib.
Proof. by move => n; rewrite fibSS. Qed.

Lemma lucas_like_fib: like_fib lucas.
Proof. by move => n; rewrite lucasSS. Qed. 

Lemma like_fib_eq F F': 
  like_fib F -> like_fib F' -> F 0 = F' 0 -> F 1 = F' 1 -> F =1 F'.
Proof.
move => ha hb hc hd n.
suff:  F n = F' n /\  F n.+1 = F' n.+1 by case.
by elim:n => // n [he hf]; split => //; rewrite ha hb he hf.
Qed.

Lemma is_fib F: like_fib F -> F 0 = 0 -> F 1 = 1 -> F =1 fib.
Proof. by move => sa sb sc; apply:like_fib_eq. Qed.

Lemma like_fib_mul F c: like_fib F -> like_fib (fun n => c * F n).
Proof. by move => h n; rewrite -mulnDr h. Qed.

Lemma like_fib_add F F': like_fib F -> like_fib F' -> 
 like_fib (fun n => F n + F' n).
Proof. by move => h1 h2 n; rewrite addnACA - h1 - h2. Qed.

Lemma like_fib_shift F m: like_fib F -> like_fib(fun n => F (n + m)).
Proof. by move => h n; rewrite !addSn h. Qed.

Lemma like_fib_succ F: like_fib F -> like_fib(fun n => F (n.+1)).
Proof. by move => h n. Qed.


Lemma like_fibE F: like_fib F -> 
   forall n, F n.+1 = (F 0) * (fib n) + (F 1) * (fib n.+1).
Proof.
move => H; apply:like_fib_eq => //=.
- by apply: like_fib_add; apply: like_fib_mul.
- by rewrite muln0 muln1.
- by rewrite H !muln1 addnC.
Qed.

Lemma like_fib_shiftE F m n: like_fib F ->
  F (n+m).+1 = F (n.+1)* fib m.+1 + F n * fib m.
Proof.
move => ha. 
by rewrite -addnS addnC (like_fibE(like_fib_shift n ha) m) add0n add1n addnC.
Qed.


Lemma lucasS n: lucas n.+1 = fib n.+1 + (fib n).*2.
Proof. by rewrite (like_fibE lucas_like_fib) addnC mul1n mul2n. Qed.

Lemma lucas_add m n: lucas (n+m).+1 = lucas (n.+1)* fib m.+1 + lucas n * fib m.
Proof. by rewrite (like_fib_shiftE _ _ lucas_like_fib). Qed.

Lemma like_fib_lucas F: like_fib F -> F 0 <= 2 * F 1 -> F 1 <=  3 * (F 0) ->
   forall n, 5 * F n = 
     (3* (F 0) - F 1) * (lucas n) + (2* (F 1) - F 0)* (lucas n.+1).
Proof.
have Ha:= lucas_like_fib.
move => h la lb. 
move: (subnK la) (subnK lb); set a := _ - _; set b := _ - _ => ea eb.
apply:like_fib_eq. 
+ exact: like_fib_mul.
+ by apply: like_fib_add; apply: like_fib_mul.
+ apply/eqP; rewrite lucas0 lucas1 muln1 -(eqn_add2l (2 * F 1)) (mulnC  b 2).
  by rewrite addnA - mulnDr (addnC _ b) eb - ea - addnA addnC  -mulSn mulnA.
+ apply/eqP;rewrite lucas1 muln1 -[lucas 2]/3  -(eqn_add2r (3 * F 0)).
  by rewrite (mulnC a) - addnA - mulnDr ea mulnA (mulSn 5) addnA eb addnC.
Qed.

Lemma lucas_fib2 n: 5 * fib n.+2 = 3 * lucas n.+1 + lucas n.
Proof.
by rewrite addnC (like_fib_lucas (F:= fun n => fib n.+2)) // mul1n.
Qed.

Lemma lucas_fib3 n: 5 * fib n.+1 = lucas n.+1 + (lucas n).*2.
Proof.
by rewrite (like_fib_lucas (F:= fun n => fib n.+1)) // addnC mul1n mul2n.
Qed.

Lemma lucas5S n: lucas (n+5) = 5 * lucas n.+1 + 3 * lucas n.
Proof. by rewrite addnS lucas_add mulnC (mulnC (lucas n)). Qed.

Lemma fib3S n: fib n.+3 = (fib n.+1).*2 + (fib n).
Proof. by rewrite fibSS fibSS addnAC addnn. Qed.

Lemma lucas3S n: lucas n.+3 = (lucas n.+1).*2 + (lucas n).
Proof. by rewrite !lucasSS addnAC addnn. Qed.

Lemma fib4S n: fib n.+4 = 3*(fib n.+1) + (fib n).*2.
Proof. by rewrite fib3S fibSS doubleD addnAC - mul2n -mulSnr. Qed.

Lemma fib_square_succ n: (fib n.+2)^2 = (fib n.+1)^2 + (fib n)*(fib n.+3).
Proof.
rewrite fibSS sqrnD mulnA mulnC -(mulnn (fib n)) -addnA -mulnDr.
by rewrite fibSS fibSS addnAC addnn mul2n (addnC (fib n)).
Qed.

Lemma fib_double n: fib ((n.+1).*2) = (fib n.+1) *((fib n).*2 + fib (n.+1)).
Proof. by rewrite fib_double_lucas lucasS addnC. Qed.


Lemma fib_square_n3_n n: fib n.+3 ^ 2 + fib n ^ 2 = (fib (n.*2.+3)).*2.
Proof.
apply/eqP.
rewrite -(eqn_add2l (fib (n.+1).*2.+1)) {1} fib_doubleS addnAC addnA.
rewrite (addnC (fib n.+2 ^ 2)) -fib_doubleS -addnA (addnC (fib n ^2)). 
by rewrite - fib_doubleS !doubleS fib3S - addnA - fibSS addnC.
Qed.

Lemma lucas_square n:
  (lucas n)^2 = (if (odd n) then subn else addn) (lucas (n.*2)) 2.
Proof.
case:n => // n.
set b :=  fib n.+1 ^ 2.
rewrite lucas_fib //= lucas_fib // !fib_doubleS - addnA sqrnD. 
rewrite (addnA b) addnn (addnC b.*2) addnA mul2n.
set a := fib n.+2 * fib n;  set c := fib n.+2 ^ 2 + fib n ^ 2.
move:(fib_sub (leqnSn n)); rewrite mulnn (subSn (leqnn n)) subnn -/b -/a => h.
have: (if odd n then a > b else b > a).  
  by case : odd h;  rewrite - subn_gt0 => <-.
rewrite -[2]/((fib 1).*2) h; case: odd  => /= /ltnW/subnK {1} <-.
  by rewrite - addnA - doubleD [in (_ + _).*2] addnC.
by rewrite doubleD addnCA addKn.
Qed.

  
Lemma like_fib_bis F: like_fib F -> F 0 <= 2 * F 1 -> 
   forall n, 2 * F n = (F 0) * (lucas n) + (2* (F 1) - F 0)* (fib n).
Proof.
have Ha:= lucas_like_fib.
move => h la. 
apply:like_fib_eq.
+ by apply: like_fib_mul.
+ by apply: like_fib_add; apply: like_fib_mul.
+ by rewrite mulnC muln0 addn0.
+ by rewrite !muln1 subnKC.
Qed.

Lemma fib_pos n: fib (n.+1) = (fib (n.+1)).-1.+1.
Proof. by rewrite prednK // fib_gt0 //. Qed.

Lemma fib_eq0 n: (fib n == 0) = (n == 0). 
Proof. by case: n => [|n]=> //=; rewrite eqn0Ngt fib_gt0. Qed.

Lemma fib_gen n: n <= fib n.+1.
Proof.
case:n => //; elim => // n IH.
by move: (leq_add IH (fib_gt0 (isT:0<n.+1))); rewrite addn1.
Qed.

Lemma lucas_gen n: n <= lucas n.
Proof.
case:n => //; elim => // n IH.
by move: (leq_add IH (lucas_gt0 n)); rewrite addn1 - lucasSS.
Qed.


Lemma fib_monotone_bis a b: fib a < fib b -> a < b.
Proof. by rewrite ltnNge; case: (ltnP a b) => // /fib_monotone ->. Qed.

Lemma fib_smonotone_bis a b: a < b -> fib a.+2 < fib b.+2.
Proof. by move => h; apply:fib_smonotone; rewrite !ltnS h. Qed.

Lemma fib_sum_bound a b n: a <=  fib n.+1 -> b <=  fib n ->
   a + b = fib n.+2 -> (a = fib n.+1) /\ (b = fib n).
Proof.
move => sa sb /esym /eqP; rewrite fibSS -(subnK sa) -(subnK sb) addnACA.
by rewrite -{2}(add0n (a+b)) eqn_add2r addn_eq0 => /andP [] /eqP -> /eqP ->. 
Qed.

Lemma fib_ge2_alt n: fib n.+3 = (fib n.+3).-2.+2.
Proof.
by rewrite - (subnK(fib_gen (n.+2))) 2!addnS.
Qed.

Lemma fib_partition a b x:
   fib a <= x < fib a.+1 -> fib b <= x < fib b.+1  -> a = b.
Proof.
move => /andP[ha hb] /andP[hc hd]; apply /eqP; rewrite eqn_leq.
move: (leq_ltn_trans ha hd) => /fib_monotone_bis; rewrite ltnS => ->.
by move: (leq_ltn_trans hc hb) => /fib_monotone_bis; rewrite ltnS => ->.
Qed.

Lemma lucas_smonotone m n: 0 < m < n -> lucas m < lucas n.
Proof.
elim: n=> [|[|n] IH]; first by rewrite andbF.
  by rewrite ltnS ltnNge; case:leq.
rewrite lucasSS andbC; case/andP; rewrite leq_eqVlt; case/orP.
  by rewrite eqSS; move/eqP=> -> H1m; rewrite -addn1 leq_add // lucas_gt0.
by move=> H1m H2m; apply: ltn_addr; apply: IH; rewrite // H2m.
Qed.

Lemma lucas_monotone m n: 0 < m <= n -> lucas m <= lucas n.
Proof.
by rewrite (leq_eqVlt m); case: eqP =>[-> // | _  /lucas_smonotone /ltnW].  
Qed.

Lemma lucas_injective: injective lucas.
Proof.
move => m n; wlog: m n / m < n.
   move => h;case: (ltngtP m n) => //; first by apply:h.
   by move => ha hb; symmetry;apply: h.
move => lt1;case:(posnP m) => mp sv; last first.
  by move/andP:(conj mp lt1) => /lucas_smonotone; rewrite sv ltnn.
move: lt1 sv; rewrite mp lucas0; case: n => [|[| n]] // _ ha.
by move/lucas_monotone: (isT:0 < 2 <= n.+2); rewrite - ha.
Qed.


Lemma lucas_injective_bis a b: (lucas a == lucas b) = (a== b).
Proof. exact: (inj_eq lucas_injective). Qed.

Lemma lucas_smonotoneE m n: 
  lucas m < lucas n = [|| (0< m < n), (m==1) && (n== 0)| (m == 0) && (2<= n )].
Proof.
case nz: (n==0).
   rewrite (eqP nz) /= leqn0; case: m => [|[|m]] //. 
   by rewrite ltnNge lucasSS (leq_add (lucas_gt0 m.+1) (lucas_gt0 m)).
case mz: (m==0).
   rewrite (eqP mz) /= lucas0; move: nz; case: n => [|[| n]] // _.
   by rewrite  -[3]/(lucas 2) lucas_monotone.
rewrite andbF /= orbF; case: (ltnP m n) => h. 
  by rewrite lucas_smonotone ?h lt0n mz.
by rewrite ltnNge lucas_monotone lt0n ?mz // nz h.
Qed.

Lemma lucas_monotoneE m n: 
  lucas m <= lucas n = 
    [|| m== n, 0< m < n, (m==1) && (n== 0)| (m == 0) && (2<= n )].
Proof. by rewrite leq_eqVlt lucas_injective_bis lucas_smonotoneE. Qed.

Lemma lucas_monotone2 n p: p <= n -> lucas (n - p) <= lucas (n + p).
Proof.
move/subnK => {2} <-; rewrite -addnA addnn lucas_monotoneE.
case pz:(p==0); first by rewrite (eqP pz) addn0 eqxx.
have p2: 2 <= p.*2 by rewrite (leq_double 1 p) lt0n pz.
rewrite (ltn_paddr _ (ltnW p2)) (leq_trans p2 (leq_addl _ p.*2)) lt0n !andbT.
by case np: (n-p==0); rewrite ? orbT.
Qed.

Lemma lucas_ge2 n: n !=1 -> lucas n = (lucas n).-2.+2.
Proof.
case:n => //; case => // n _.  
by rewrite -(subnK (lucas_gen n.+2)) 2! addnS.
Qed.                        

Lemma lucas_ge2d n: 1 < lucas (n.*2).
Proof. by rewrite lucas_ge2 => //; case:n. Qed.

Lemma lucas_powge2 n: 1 < lucas (2 ^ n.+1) ^ 2.
Proof. by rewrite -{1}[1]/(1^2) ltn_sqr expn2S lucas_ge2d. Qed.

Lemma lucas_square' n: 
  lucas (n.*2) =  (if (odd n) then addn else subn) ( (lucas n)^2) 2.
Proof.
by rewrite lucas_square; case: odd; rewrite ? addnK // subnK // lucas_ge2d.
Qed.

Lemma lucas_pow2_odd n: odd (lucas (2^n)).
Proof.
elim: n => // n on; rewrite expn2S lucas_square'. case: n on=> // n.
by rewrite {2} expn2S odd_double odd_sub ?lucas_powge2 // odd_sqr => ->.
Qed.

Lemma lucas_pow2_mod4 n: lucas (2^(n.+1)) = 3 %[mod 4].
Proof.
case: n => // n; rewrite expn2S lucas_square' {1} expn2S odd_double.
have aux:= (square_odd_mod4(lucas_pow2_odd n.+1)).
by apply/eqP; rewrite -(eqn_modDr 2) subnK ?lucas_powge2 // aux.
Qed.

Lemma coprimeSn_fib n: coprime (fib n) (fib n.+1) .
Proof. by elim:n =>// h; rewrite /coprime fibSS  gcdnDl gcdnC. Qed.

Lemma gcd_fib n m: gcdn (fib n) (fib m) = fib (gcdn n m).
Proof.
move: (leq_maxl n m) (leq_maxr n m);move:(maxn _ _)=> k. 
elim: k n m; [ by case; [case  |] | move => max Hrec n m le1 le2 ].
wlog lmn: n m le1 le2 / n < m.
  move => H; case: (ltngtP n m) => aux; first by apply: H. 
    by rewrite gcdnC (gcdnC n); apply: H.
  by rewrite aux !gcdnn.
case (posnP n); first by move => ->; rewrite!  gcd0n.
move:(subnK (ltnW lmn));set r := m - n => eq1 np.
move:(lmn); rewrite - subn_gt0 lt0n => rnz.
move:(ltn_sub2l (ltn_trans np lmn) np); rewrite subn0 => ha.
rewrite -eq1 gcdnDr fib_add // gcdnMDl (Gauss_gcdl _ (coprimeSn_fib n)). 
by rewrite Hrec // - ltnS; apply: (leq_trans _ le2).
Qed.

Lemma mod3_small n: (n %% 3)  < 3.
Proof. by rewrite ltn_pmod. Qed.

Lemma fib_is_even_mod3 n: odd (fib n)  =  (n %%3 !=0). 
Proof.
move: (gcd_fib n 3); rewrite - (gcdn_modl n) gcd_n2. 
move:(mod3_small n);case:(n %% 3) => [|[|[| k]]] //= _; case: odd => //.
Qed.

Lemma lucas_is_even_mod3 n: odd (lucas n)  =  (n %%3 !=0). 
Proof.
rewrite - fib_is_even_mod3; case:n => // n.
by rewrite lucasS odd_add odd_double addbF.
Qed.

Lemma gcd_lucas_fib1 n: gcdn (lucas n.+1) (fib n.+1) = fib (gcdn n.+1 3).
Proof.
have h: coprime (fib n.+1) (fib n) by rewrite coprime_sym coprimeSn_fib.
by rewrite gcdnC lucasS gcdnDl - muln2 Gauss_gcdr //(gcd_fib _ 3).
Qed.

Lemma gcd_lucas_fib2 n:  (n %%3 ==0) -> gcdn (lucas n) (fib n) = 2.
Proof.
by case: n => // n H; rewrite gcd_lucas_fib1 - (gcdn_modl) (eqP H).
Qed.

Lemma gcd_lucas_fib3 n: (n %%3 !=0) -> coprime (lucas n) (fib n).
Proof.
case: n => // n H; rewrite /coprime gcd_lucas_fib1 - (gcdn_modl).
by move: (mod3_small n.+1) H; case: (n.+1 %% 3) => [|[ | [| ]]].
Qed.

Lemma fib_mod3 n: 3 %| (fib n) =  (4 %| n).
Proof.
pose p n := (3 %| fib n) = (4 %| n).
suff: [/\ p n, p n.+1, p n.+2 & p n.+3] by case.
elim: n => // n [ha hb hc hd]; split => //.
move: ha;rewrite /p fib4S - (addn4 n) /dvdn  modnDr mulnC modnMDl.
move => <-; rewrite - addnn - modnDm.
by move: (mod3_small (fib n)); case: (fib n %% 3) => [|[|[|]]].
Qed.

Lemma lucas_mod3 n: 3 %| (lucas n) = (n== 2 %[mod 4]).
Proof.
case:n => [| [| n ]] //.
rewrite -{3} (add0n 2) - {2} (addn2 n) eqn_modDr - (add1n n) lucas_add /dvdn.
rewrite mul1n mulnC modnMDl; exact:fib_mod3.
Qed.

Lemma sum_fib_pascal n:
  \sum_(i<n.+1) 'C(n,i)* fib i = fib(n.*2) /\ 
  \sum_(i<n.+1) 'C(n,i)* fib i.+1 = fib(n.*2.+1).
Proof.
elim:n; first by rewrite !big_ord_recr  !big_ord0 /= //.
move =>n [He Ho]; split.
  rewrite big_ord_recl muln0 add0n doubleS fibSS - Ho.
  have ->: fib n.*2 = \sum_(i < n.+1) 'C(n, i.+1) * fib i.+1.
    by rewrite -He big_ord_recl big_ord_recr muln0 add0n bin_small //= addn0.
  by rewrite addnC -big_split; apply:eq_bigr=> i _ /=; rewrite - mulnDl/= binS.
rewrite doubleS fibSS fibSS -Ho - He big_ord_recl bin0 muln1 /=.
transitivity (\sum_(i < n.+1) 'C(n, i) * fib (bump 0 i).+1 
   + \sum_(i < n.+2) 'C(n, i) * fib i.+1).
  rewrite (big_ord_recl (n.+1)) bin0 muln1 [RHS] addnC - addnA; congr addn.
  by rewrite -big_split; apply:eq_bigr=> i _ /=; rewrite - mulnDl/= binS.
rewrite (big_ord_recr (n.+1)) bin_small //= addn0;congr addn.
by rewrite -big_split; apply:eq_bigr=> i _ /=; rewrite - mulnDr/= fibSS.
Qed.

Lemma fib_lt_lucas n: n != 0 -> fib n <= lucas n ?= iff (n==1).
Proof.
move => h; rewrite (lucas_fib h); move: h; case:n => // n _.
rewrite fibSS /= - addnA addnn eqSS; apply/leqifP.
by case:(posnP n) => np; rewrite ? np // ltn_paddr // double_gt0 fib_gt0.
Qed.

Lemma lucas_ge_2fib n: 2 <= n -> (fib n).*2 <= lucas n.
Proof. 
case:n => [|[| n]] //_; rewrite lucas_fib // -addnn (fibSS n.+1).
rewrite {2} fibSS addnA leq_add2l fib_monotone //=.
Qed.

Lemma lucas_lt_fib n: n != 0 -> lucas n <= fib n.+2 ?= iff (n==2).
Proof.
move => h; rewrite (lucas_fib h) fibSS; apply/leqifP. 
move:h; case:n =>[ | [| [| n]]] //= _ ;rewrite ltn_add2l fib_smonotone //=.
Qed.

Lemma fib_mon1 n: 2 <= n -> 3* fib n <= 2 * fib n.+1.
Proof.
case: n => [|[|n _]]//; rewrite (fibSS n.+1)mulnDr mulSnr leq_add2l.
by rewrite fibSS mul2n - addnn leq_add2l fib_monotone.
Qed.

Lemma lucas_mon1 n: 3 <= n -> 3* lucas n <= 2 * lucas n.+1.
Proof.
case: n => [|[|n ]]//;rewrite (lucasSS n.+1) mulnDr mulSnr leq_add2l !ltnS => h.
rewrite lucasSS mul2n - addnn leq_add2l lucas_monotone ?h //=.
Qed.

Lemma fib_square_bound n: 2 <= n -> fib n.*2 < (fib n.+1)^2 < fib n.*2.+1.
Proof.
move => ha;rewrite fib_doubleS -{2}(addn0 ((fib n.+1)^2)) ltn_add2l sqrn_gt0.
rewrite (fib_gt0 (ltnW ha)) andbT.
rewrite -(ltn_add2l (fib n.+1 * (fib n).*2)) -mulnn -mulnDr. 
rewrite -fib_double doubleS fibSS ltn_add2r fib_doubleS -muln2 mulnA mulnC.
have hb: fib n < fib n.+1 by rewrite fib_smonotone // ha leqnn.
by move/leqifP:(nat_Cauchy (fib n.+1) (fib n)); rewrite (gtn_eqF hb).
Qed.

Lemma lucas_square_bound n: 3 <= n -> 
  fib n.*2.+1 < (lucas n)^2 < fib n.*2.+2.
Proof.
rewrite lucas_square.
have ha k:  2 < fib k .+1.+4 by rewrite (fib_smonotone_bis (a:=1)) //.
case: (odd_dichot n) => -> /=; rewrite odd_double /=.
  case: (n./2) => //k _; rewrite !doubleS lucas_fib //;have hb:= (ha k.*2.*2).
  rewrite -(subnK (ltnW hb)) addnA addnK ltn_paddr ? subn_gt0 //.
  rewrite (fibSS (k.*2).*2.+4.+2) ltn_add2l (fibSS  (k.*2).*2.+4). 
  by apply /(leq_ltn_trans (leq_subr 2 _)) /ltn_paddr /fib_gt0.
case:(n./2) => [// | [// | m _]].
rewrite !doubleS lucas_fib //; set k :=  (m.*2).*2.+4.+2.
by rewrite - addnA {1} addn2 ltn_paddr //= (fibSS k.+2) (fibSS k) !ltn_add2l ha.
Qed.

Lemma fib_lt_exp n: 2 <= n -> fib n.+2 < 2^n.
Proof.
move/ subnK => <-.
pose p k := fib (k + 2).+2 < 2 ^ (k + 2).
suff: p (n-2) /\ p (n-2).+1 by case.
elim: {n} (n -2) => // k [ha hb]; split => //.
move:(leq_add hb (ltnW ha));rewrite /p !addSn - fibSS => sa.
apply: (leq_trans sa). 
by rewrite (expnS _ _.+1) mul2n -addnn leq_add2l leq_exp2l.
Qed.



(* -- *)

Lemma fib_lucas1 j k: j <= k ->
  lucas j * fib k =
    (if (odd j) then subn else addn) (fib (k + j)) (fib (k - j)).
Proof.
case:j; first by rewrite /= addn0 subn0 mul2n addnn.
move => j;rewrite leq_eqVlt; case/orP => ljk.
  rewrite (eqP ljk) mulnC - fib_double_lucas addnn subnn fib0.
  by case: odd => //; rewrite ?subn0 ?addn0.
have hb: 0 < fib (k - j.+1) by rewrite fib_gt0 //subn_gt0.
have ha:=(fib_sub (ltnW ljk)).
rewrite mulnC lucas_fib // (addnC k) fib_add // mulnDr addnC.
rewrite (mulnC _ (fib k))  (mulnC _ (fib k.+1)); move: ha; simpl.
case:odd => /= ha; rewrite ha.
  by rewrite - addnA subnKC // ltnW // -subn_gt0 -ha.
have hc : fib k * fib j.+2 < fib k.+1 * fib j.+1 by rewrite - subn_gt0 -ha.
by rewrite - {1} (subnKC (ltnW hc)) addnA addnK.
Qed.

Lemma fib_lucas2 j k: k <= j ->
  lucas j * fib k =
    (if (odd k) then addn else subn) (fib (k + j)) (fib (j - k)).
Proof.
case:j; first by rewrite leqn0 => /eqP ->.
move => j;rewrite  leq_eqVlt; case/orP => ljk.
  rewrite (eqP ljk) mulnC - fib_double_lucas addnn subnn fib0.
  by case: odd; rewrite ?subn0 ?addn0.
have hb: 0 < fib (j.+1 - k) by rewrite fib_gt0 //subn_gt0.
rewrite addnC fib_add // lucas_fib // mulnDl // addnC.
move: (fib_sub (ltnW ljk))=> ha; rewrite ha /=;move: ha; case:odd => ha.
  by rewrite -addnA subnKC // ltnW // -subn_gt0 -ha.
have: (fib j.+2 * fib k < fib j.+1 * fib k.+1) by rewrite - subn_gt0 -ha.
by move => /ltnW/subnKC {1} <-; rewrite addnA addnK.
Qed.

Lemma lucas_lucas1 p n: p <= n ->
  lucas n * lucas p =
    (if (odd p) then subn else addn) (lucas (n + p)) (lucas (n - p)).
Proof.
case: n; first by rewrite leqn0 => /eqP -> //.
move => n; rewrite leq_eqVlt; case/orP; rewrite ?ltnS => ha.
  by rewrite - (eqP ha) addnn subnn mulnn lucas_square.
rewrite mulnC (@lucas_fib n.+1) //=  mulnDr subSn //.
rewrite (fib_lucas1 (leqW (leqW ha))) (fib_lucas1 ha) lucas_fib //lucas_fib //.
rewrite (subSn (leqW ha)) (subSn ha) addSn addSn /=. 
case:odd; last by rewrite addnACA.
have hb:=leq_BD n p.  
have/subnK {2}<-: fib (n - p) <= fib (n + p) by apply: fib_monotone. 
have: fib (n - p).+2 <= fib (n + p).+2 by  apply: fib_monotone; rewrite !ltnS.
by move/subnK => {2} <-; rewrite addnACA addnK. 
Qed.

Lemma lucas_lucas2 p n: p <= n ->
  5 * fib n * fib p =
    (if (odd p) then addn else subn) (lucas (n + p)) (lucas (n - p)).
Proof.
elim: p {-2} p (leqnn p) => [p|p IHp p0].
  by rewrite leqn0; move/eqP=>-> /=; rewrite /= addn0 subn0 subnn muln0.
rewrite leq_eqVlt; case/orP=> [|Hn1]; last by apply: IHp; rewrite - ltnS.
move /eqP => -> lnp.
case wwa: (p == 0).
   move: lnp; rewrite (eqP wwa)  => /subnK {1 2} <- /=.
   by rewrite muln1 addn1 addn1 lucasSS - addnA addnn lucas_fib3.
case wwb: (p == 1).
   move: lnp; rewrite (eqP wwb)  => /subnK {1 2} <- /=.
   set x := lucas (n - 2).+1.
   rewrite addn2 addn2 3!lucasSS muln1 lucas_fib2 (addnC x) - (addnA _ x x).
   by rewrite addnn - addnACA -mul2n -(mulSnr 2 x) - addnA addKn addnC.
have Hg: (lucas (n - p.+1).+2).*2 = lucas (n - p.+1) + lucas (n - p.+1).+3. 
  by rewrite addnC [in RHS] lucasSS - addnA -lucasSS addnn.
case: (odd_dichot p) => pv; rewrite pv /= odd_double /=.
  case (posnP p./2) => ww; first by move: wwb; rewrite pv ww. 
  move: (prednK ww) => eq1.
  have Ha: (p./2.-1).*2 < p by rewrite {2} pv ltnS leq_double leq_pred.
  have Hb: (p./2.-1).*2 < n by rewrite (ltn_trans  Ha lnp).
  have Hc: (p./2).*2 <= p by apply: double_half_le.
  have Hd:= (leq_trans Hc (ltnW lnp)).
  have He: (p./2.-1).*2.+4 <= n by rewrite - doubleS eq1 - pv.
  rewrite fibSS mulnDr -{1} eq1 doubleS fibSS - doubleS eq1.
  rewrite mulnDr addnAC addnn IHp // IHp // /= !odd_double /=.
  rewrite - {1 2 5 6} eq1 doubleS ! addnS 2! [in RHS] lucasSS  addnAC addnn.
  rewrite - {2 4}(subnK He) -2!addSnnS addnK - addSnnS addnK -doubleS eq1 -pv.
  set A := (lucas (n + (p./2.-1).*2).+2).*2.
  have lt1: lucas (n - p.+1) + lucas (n - p.+1).+3 <= A.
     rewrite - Hg /A leq_double; apply: lucas_monotone => /=.
     by apply: (@leq_trans n.+2); rewrite !ltnS ? leq_subr // ?leq_addr.
  move/ (leq_sub2r (lucas (n - p.+1))): (lt1); rewrite addKn => lt2.
  rewrite doubleB Hg subnDA addnC - addnA subnKC // [in RHS] addnC - addnBA //. 
  apply: leq_trans lt1; apply leq_addr.
case (posnP p./2) => ww; first by move: wwa; rewrite pv ww. 
move: (prednK ww) => eq1; rewrite - eq1 doubleS.
have Ha: (p./2.-1).*2 < p by rewrite {2} pv ltn_double eq1.
have Hc := leq_trans Ha (ltnW lnp).
have Hb:= ltnW Ha; have Hd:= ltnW Hc.
have Ht: (n - (p./2.-1).*2) = (n-p.+1).+3.
  by rewrite -3! subSS - doubleS eq1 - pv -{1} (subnK lnp) - 3!addSn addnK.
have He: lucas (n - p.+1).+3 <= lucas (n + (p./2.-1).*2).
  apply: lucas_monotone; rewrite /= - Ht; apply: leq_BD.
have Hf: (p./2.-1).*2.+3 <= n by rewrite -doubleS eq1 - pv.
rewrite fibSS fibSS addnC addnA addnn mulnDr - doubleMr IHp // IHp //=.
rewrite odd_double /= doubleD !addnS lucasSS lucasSS [ X in _ = X + _] addnAC. 
have ->: (n - (p./2.-1).*2.+3) = n - p.+1 by  rewrite - doubleS eq1 - pv.
have ->: (n - (p./2.-1).*2.+1) = (n-p.+1).+2.
  by rewrite -2! subSS - doubleS eq1 - pv -{1} (subnK lnp) - 2!addSn addnK.
rewrite addnn -!addnA Ht (addnBA _ He) Hg; congr addn. 
by rewrite addnC addnA addnK.
Qed.

Lemma lucas_lucas3 n p:
  (lucas (n + p)).*2 = lucas n * lucas p + 5 * fib n * fib p.
Proof.
wlog cp: n p / p <= n.
   move => H; case/orP: (leq_total p n); first by apply:H.
   by move => ha; rewrite addnC mulnC mulnAC H.
have ha:= (lucas_monotone2 cp).
rewrite (lucas_lucas2 cp) (lucas_lucas1 cp) - addnn.
by case: odd; [rewrite addnCA subnK  | rewrite -addnA subnKC ].
Qed.

Lemma lucas_lucas4 n p:
  (fib (n + p)).*2 = lucas n * fib p +  lucas p  * fib n.
Proof.
wlog le1: n p / p <= n.
   move => H; case/orP: (leq_total p n); first by apply:H.
   by move => ha; rewrite addnC H // addnC. 
have ha: fib (n - p) <= fib (n + p) by apply: fib_monotone; apply:leq_BD.
rewrite (fib_lucas1 le1) (fib_lucas2 le1) -addnn (addnC p).
by case: odd; [ rewrite - addnA subnKC | rewrite addnCA subnK].
Qed.


Lemma lucas_is_square n x: (lucas n) == x^2  = 
   ((n==1) &&(x==1 )) || (n==3) && (x==2).
Proof.
apply/idP/idP; last by case/orP => /andP[/eqP -> /eqP ->].
have Hb:[\/ x ^2 == 0 %[mod 8], (x ^2 == 1 %[mod 8]) | x ^2 == 4 %[mod 8] ].
  have H a b: (a.*2.*2 +b)^2 = b ^2 %[mod 8].
    rewrite sqrnD addnAC -2!mul2n mulnA expnMn -[(2 * 2) ^ 2]/(8 * 2).
    by rewrite 2! (mulnA 2) -[2*(2*2)]/8 - 2!mulnA - mulnDr mulnC modnMDl. 
  case:(odd_dichot x); case:(odd_dichot x./2)=> -> ->; set y := x./2./2.
  - by constructor 2; rewrite doubleS - addn3 H.
  - by constructor 2; rewrite - addn1 H.
  - by constructor 3; rewrite doubleS - addn2 H.
  - by constructor 1; rewrite - (addn0 (y.*2).*2) H.
have Ha a b: lucas (12 * a + b) = lucas b %[mod 8].
  suff Hc c: lucas (12 + c) = lucas c %[mod 8].
    by elim: a => // a hr; rewrite mulnS -addnA Hc hr.
  case:c => // c. 
  rewrite addnS addnC lucas_add fibSS addnC mulnDr addnA -mulnDl.
  rewrite -[fib 12]/(18 *8) mulnA modnMDl -[fib 11]/(11*8 +1).
  by rewrite  mulnDr  mulnA modnMDl muln1.
move: (divn_eq n 12); set a := n %/ 12; set b := n %% 12 => nv.
move => eq1; case:(odd_dichot n) => eq2; last first.
  move:(lucas_square n./2); rewrite - eq2 (eqP eq1);case: odd.
    move => h; case:(ltnP (x^2) 2) => sa.
      move: h; rewrite (eqP (ltnW sa)) => sb.
      by move: (lucas_gt0 n./2); rewrite - ltn_sqr sb.
    by move:(subnK sa); rewrite - h => /square_plus2_square.
  by move/esym /square_plus2_square.
move: (f_equal odd nv);rewrite eq2 /= -[12]/(6.*2)odd_add odd_mul !odd_double.
rewrite andbF /= => ob.
(*
have ob: odd b.
  move: (f_equal odd nv);rewrite eq2 /= -[12]/(6.*2)odd_add odd_mul !odd_double.
  by rewrite andbF /=.
*)
have Hc: ((b==1) || (b==3) || (b== 9)).
  move: (Ha a b);  move: (ltn_pmod n (ltn0Sn 11)).
  rewrite mulnC -nv (eqP eq1) -/b; move: ob Hb; clear.
  case:b => [| [|[|[|[| [| [|[|[|[| [| [| ]]]]]]] ]]]]] // _ Hb _.
  - by rewrite -[lucas 5]/(3 + 1 *8) addnC modnMDl => w; case Hb; rewrite w.
  - by rewrite -[lucas 7]/(5 + 3 *8) addnC modnMDl => w; case Hb; rewrite w.
  - by rewrite -[lucas 11]/(7 + 24 *8) addnC modnMDl => w; case Hb; rewrite w.
set y := lucas (3*a + 4).
have: lucas (12 * a + 9) =  y * (y^2 +1).

simpl.

Abort.


Lemma lucas_n_fib_mod5 n: n * lucas n == fib n %[mod 5].
Proof.
pose Y n := n * lucas n - fib n.
have Hx m: m != 0 -> fib m <= m * lucas m.
  move => h; apply:(@leq_trans (lucas m)); first by apply:fib_lt_lucas.
  by apply:leq_pmull; rewrite lt0n.
have Ha: forall n, n != 0  ->  n * lucas n = fib n + Y n.
  move => m /Hx h; rewrite /Y subnKC //. 
have Hb x y z:  x + z = y -> x = y - z by move => <-; rewrite  addnK.
have Hc a b: a = 0 %[mod 5] -> b = 0  %[mod 5]  -> a.*2+b = 0 %[mod 5]. 
  by move => sa sb; rewrite - modnDm - addnn - (modnDm a a 5) sa sb mod0n.
have Hd a b: a = 0 %[mod 5] -> b = 0  %[mod 5]  -> a-b = 0 %[mod 5]. 
  move => sa sb; case/orP:(leq_total a b); first by rewrite -subn_eq0 => /eqP->.
  by move/subnKC=> sc; move: sa; rewrite -{1}sc -modnDm sb mod0n add0n modn_mod.
suff Hf : forall m, Y m.+4 = ((Y m.+3).*2 + Y m.+2) - ((Y m.+1).*2 + Y m).
  case nz:(n== 0);  rewrite ? (eqP nz) // -(addn0 (fib n)) Ha ? nz // eqn_modDl.
  suff: (forall k, k <= n.+3 -> Y k = 0 %[mod 5]).
    by move => h; apply/eqP /h /ltnW /ltnW.
  clear nz;elim: n; first by case => [|[|[|[| ]]]].
  move => n Hrec k.
  have ha: n < n.+3 by apply/ltnW/ltnW. 
  have hb := (ltnW ha).
  rewrite (leq_eqVlt); case/orP; last by rewrite ltnS; apply: Hrec.
  move => /eqP ->; rewrite Hf; apply: Hd; apply: Hc;apply: Hrec => //.
have He m: m!=0 -> (Y m.+1).*2 + Y m = (m.+1 * lucas m.+1).*2 + m * lucas m  -
   ((fib m.+1).*2 + fib m).
  move => h; apply: Hb. 
  rewrite addnACA -doubleD (addnC (Y m)) - Ha // (addnC (Y m.+1)) - Ha //.
move => m; case mz: (m==0); first by rewrite (eqP mz).
have mz' := (negbT mz).
set x1 := (m.+1 * lucas m.+1).*2 + m * lucas m.
set x2 := (fib m.+1).*2 + fib m.
set x3  := (m.+3 * lucas m.+3).*2 + m.+2 * lucas m.+2.
set x4 := (fib m.+3).*2 + fib m.+2.
have la: x2 <= x1 by rewrite /x1 /x2; apply: leq_add; rewrite ? leq_double Hx.
apply: (Hb); rewrite ! He //; apply: (Hb);rewrite addnAC (addnBA _ la). 
symmetry;apply:(Hb);rewrite -/x3 -/x4 - addnA [RHS]addnC (addnBA _ (Hx _ _)) //.
apply:Hb;rewrite /x1 /x2 /x3 /x4; clear.
rewrite (addnC _ ((fib m.+1).*2 + fib m)) addnAC - [in RHS] addnA; congr addn.
  by rewrite -fib3S - fib3S addnC -fibSS.
rewrite {1} [m.+3] (addnC 3 m) {1} [m.+4] (addnC 4 m) !mulnDl doubleD doubleMr.
rewrite addnAC {2} [m.+2] (addnC 2 m) mulnDl addnA - mulnDr (mulSn m) addnA.
rewrite - (addnA _.*2) - mulnDr doubleD (doubleMr m)  - (addnA _.*2) - mulnDr.
rewrite (addnC (lucas m.+1).*2) -addnA - addnA; congr (m *_  + _).
   by rewrite -lucas3S addnA - lucas3S addnC -lucasSS.
(* alt proof:
   have h := like_fib_lucas.
   rewrite -2!mul2n mulnA - (addn4 m) -(addn3 m) -(addn2 m) - (addn1 m).
   by move:m; apply: like_fib_eq => //;
     apply: like_fib_add; apply:like_fib_mul;apply:like_fib_shift. *) 
rewrite -(mulnA 2 2) ! mul2n - !doubleD; congr double.
rewrite (lucasSS m.+2) doubleD addnA addnAC mulSn mul2n addnA; congr addn.
by rewrite addnC - lucasSS lucas3S addnC.
Qed.


Section DiophanteEquation.

Definition DE_eq1 c d := c^2 = d^2 + c*d + 1.
Definition DE_eq2 c d := c^2 +1 = d^2 + c*d.


Lemma DE2_rec c d:  DE_eq2 c d <-> DE_eq2 (c.*2 +d) (c+d).
Proof.
rewrite /DE_eq2 -{1}addnn -addnA (addnC c) sqrnD -addnA -addnA (addnC(_ * _) 1).
rewrite (addnA (c^2))  mul2n doubleMr (addnC (_ + 1)) (mulnC _ c.*2) addnA.
rewrite mulnDl (addnA ((c + d) ^ 2)) (addnC (d^2)) mulnC - mulnn -mulnDr.
by split; [ move => -> | move/eqP; rewrite eqn_add2l => /eqP].
Qed.

Lemma DE2_lt0d c d: DE_eq2 c d -> 0 <d.
Proof.
rewrite /DE_eq2 =>h;case:(posnP d) => dp //.
by move /eqP: h; rewrite dp muln0 addn0 exp0n // addn_eq0 andbF.
Qed.

Lemma DE2_pos c d: 0 < c -> DE_eq2 c d -> d <= c < d.*2.
Proof.
move => ha hb.
move: (leq_mul ha (DE2_lt0d hb)); rewrite -(leq_add2l (d^2)) - hb. 
rewrite leq_add2r leq_exp2r // => -> /=.
case: (ltnP c d.*2) => // hc.
have ea: 4 * d^2 <= c^2 by rewrite -[4]/(2^2) -(expnMn 2) mul2n leq_exp2r.
have eb: 4 * (c * d) <= 2 * c^2. 
  by rewrite  -[4]/(2*2) mulnACA (mul2n d) -mulnn mulnA leq_mul2l hc orbT.
move: (leq_add ea eb); rewrite -mulnDr -hb mulnDr -mulSn mulSnr.
by rewrite -[X in _ <= X](addn0) -addnA leq_add2l addnS ltn0.
Qed.

Lemma DE2_rec' c d: 0 < c -> DE_eq2 c d -> DE_eq2 (c-d) (d.*2-c).
Proof.
move => cp h.
move /andP:(DE2_pos cp h) => [ea eb];apply/DE2_rec.
have xv:=(subnK ea).
move/eqP: (subnK (ltnW eb)); rewrite -addnn - {2}xv addnA eqn_add2r  addnC. 
by rewrite -addnn -addnA;move/eqP ->; rewrite xv.
Qed.

Lemma DE2_solution c d: DE_eq2 c d <-> 
     (c=0 /\ d = 1) \/ exists n, c = fib n.*2.+2 /\ d = fib n.*2.+1.
Proof.
split; last first.
  case; [ by move => [-> ->] | move => [n [-> ->]]].
  by elim:n => // n /DE2_rec;  rewrite - fib3S - fibSS !doubleS. 
elim: c d {-2} c (leqnn c).
  move => d c; rewrite leqn0 /DE_eq2 => /eqP ->.
  rewrite {1} /expn /= addn0 add0n -{1} [1]/(1^2).
  by move/eqP; rewrite eqn_sqr => /eqP ->; left.
move => n Hrec d c. 
rewrite leq_eqVlt ltnS; case /orP => [ha hb | le]; [right | by apply:Hrec ].
have cp: 0 < c by rewrite (eqP ha).
move /andP: (DE2_pos cp hb) => [la lb].
have hc:= (DE2_rec' cp hb).
have he: c - d <= n by rewrite (eqP ha) -(prednK (DE2_lt0d hb)) subSS leq_subr.
move: (subnK (ltnW lb)) (subnK la); set a := c -d; set b := d.*2 - c => xv yv.
have ra: d = a + b. 
  by apply/eqP; rewrite - (eqn_add2r d) addnn - xv addnAC yv addnC.
have rb: c = a.*2 + b by rewrite - yv ra addnA addnn.
case: (Hrec _ _ he hc).
   by move => [sa sb]; exists 0; rewrite ra rb /a/b sa sb.
move => [m [sa sb]]; exists m.+1.
by rewrite ra rb /a/b sa sb -fibSS -fib3S !doubleS.
Qed.

Lemma DE_equiv_12 c d: DE_eq1 c d <-> DE_eq2 (c+d) c.
Proof.
rewrite /DE_eq2 sqrnD mulnDl mulnn (mulnC d) -addnA mul2n -addnn (addnAC _ _ 1).
rewrite addnA -(addnA (c^2)) (addnA (d^2)) addnAC addnC.
by split; [ move => -> | move/eqP; rewrite eqn_add2r => /eqP ].
Qed.

Lemma DE1_solution c d: DE_eq1 c d <-> 
   exists n, c = fib n.*2.+1 /\ d = fib n.*2.
Proof.
split; last first.
   move => [n [-> ->]];apply /DE_equiv_12; rewrite - fibSS.
   by apply/DE2_solution; right; exists n.
case/DE_equiv_12/DE2_solution => [[/eqP] | [n [sa sb]]].
  by rewrite addn_eq0 => /andP[/eqP ->].
by exists n; move/eqP: sa; rewrite fibSS - sb eqn_add2l => /eqP ->.
Qed.

Lemma DE1_sol n:
   (fib n.*2.+1)^2 = (fib n.*2)^2 + (fib n.*2.+1)*(fib n.*2) + 1.
Proof. by apply/DE1_solution; exists n. Qed.

Lemma DE2_sol n:
   (fib n.*2.+2)^2 + 1 = (fib n.*2.+1)^2 + (fib n.*2.+2)*(fib n.*2.+1).
Proof. by apply/DE2_solution; right; exists n. Qed.


Definition DE_eq3 y z := (z^2 == (y.+1)^2 + (y.*2)^2).
Definition DE_eq4 y z := (z^2 == (y.-1)^2 + (y.*2)^2).

Lemma DE_eq3_solution y z: DE_eq3 y z <-> 
   (exists n, y = fib n.*2 * fib n.*2.+1 /\ z = fib (n.*2).*2.+1).
Proof.
split; last first.
  move => [n [-> ->]]; rewrite /DE_eq3 fib_doubleS.
  set a := fib n.*2.+1; set b :=  fib n.*2.
  have lea:  b^2 <= a ^2 by rewrite leq_sqr fib_monotone.
  rewrite (sqrnD_sub' lea) -expnMn -[4]/(2^2) -expnMn mul2n mulnC addnC.
  rewrite eqn_add2r eqn_sqr -(eqn_add2r (b^2)) subnK // addnC.
  by rewrite -(addn1 (_ * _)) addnA mulnC - DE1_sol.
case: (posnP y) => lt1 h.
  rewrite lt1; exists 0; split => //; rewrite fib1.
  by move: h; rewrite /DE_eq3 lt1 addn0 eqn_sqr => /eqP.
set r := gcdn y.+1 y.*2.
have: (y.+1)^2 + (y.*2)^2 = z^2 by rewrite (eqP h).
case/pythagore_tripleB.
+ by move => []. 
+ by move => []; move: lt1;case:(y).
+ move => [p [q [ha /ltnW hb hc hd]]]; case; case; rewrite -/r => e1 e2 e3.
  move /eqP: e2; rewrite -doubleMr eqn_double => /eqP e2.
  move: (dvdn_gcd r y y.+1); rewrite -{1} addn1 gcdnDl gcdn1 e1 e2.
  rewrite {2 3} /dvdn !modnMr eqxx /= dvdn1 => /eqP r1.
  move: e1 e2 e3; rewrite r1 !mul1n => e1 e2 e3.
  have l1: q^2 <= p^2 by rewrite leq_exp2r ? hb.
  move: (subnK l1); rewrite - e1 e2 addSn addnC - addn1; move/esym.
  move/(DE1_solution p q) => [n [ra rb]]; exists n.
  by rewrite e3 ra rb mulnC - fib_doubleS.
+ have : ~~ odd y.+1 by rewrite e2 - doubleMr odd_double. 
  move => /= /negbNE oy.
  have g2: r = 2.
    rewrite /r -(odd_double_half y) oy add1n -doubleS -!muln2 - muln_gcdl.
    by rewrite (muln2 y./2) -addnn -addSn gcdnDl (eqP (coprimeSn y./2)).
  move: (pythagore_gcd hb hc hd).
  set p1 := p + q; set q1 := p - q.
  have pv: p.*2 = p1 + q1 by rewrite -addnn -{2} (subnKC hb) addnA.
  have qv: q.*2 = p1 - q1 by rewrite subnBA// - addnA addKn addnn.
  move/eqP: e1; rewrite g2 mul2n eqn_double subn_sqr => /eqP e1.
  move: e2; rewrite g2 doubleMr qv mulnA mul2n pv mulnC -subn_sqr e1 => e2.
  have: DE_eq1 p1 q1.
    by rewrite /DE_eq1 -addnA addn1 mulnC e2 subnKC // leq_exp2r // leq_BD.
  move/(DE1_solution) => [n [p1v p2v]].
  have yv: y =  fib n.*2 * fib n.*2.+1 by rewrite e1 -/p1 -/q1 p1v p2v.
  have : 2 * z = 2* fib (n.*2).*2.+1. 
   rewrite e3 g2 mulnA mulnDr -[2*2]/(2^2) -!expnMn !mul2n pv qv p1v p2v -fibSS.
    by case:(n)=> // m; rewrite doubleS (fibSS m.*2.+1) addKn fib_square_n3_n.
  move/eqP; rewrite !mul2n eqn_double => /eqP zv.
  by exists n; rewrite - yv - e1.
Qed.

Lemma DE_eq4_solution y z: 0 < y -> 
  (DE_eq4 y z <-> 
   exists n, y = fib n.*2.+2 * fib n.*2.+1 /\ z  = fib (n.*2).*2.+3).
Proof.
move => yp; split; last first.
  move => [n [-> ->]]; rewrite /DE_eq4 - doubleS fib_doubleS.
  set a := fib n.*2.+2 ; set b := fib n.*2.+1.
  have lea:  b^2 <= a ^2 by rewrite leq_sqr fib_monotone.
  have /prednK ww : 0 < a * b by rewrite muln_gt0 !fib_gt0.
  rewrite (sqrnD_sub' lea) -expnMn -[4]/(2^2) -expnMn mul2n mulnC addnC.
  rewrite eqn_add2r eqn_sqr -(eqn_add2r (b^2)) subnK // addnC mulnC.
  by rewrite - eqSS - addnS ww - (DE2_sol n) addn1.
have yn := (prednK yp).
move => h.
have h': (y.-1)^2 + (y.*2)^2 = z^2 by rewrite (eqP h).
case:(pythagore_tripleB h'). 
+ by move  => [/eqP]; rewrite - eqSS yn =>/eqP -> <-; exists 0. 
+ by move => []; move: yp; case: (y) => //.
+ move=> [p [q [ha /ltnW hb hc hd]]]. 
  case; case; set r := gcdn y.-1 y.*2 => e1 e2 e3.
  move /eqP: e2; rewrite -doubleMr eqn_double => /eqP e2.
  move: (dvdn_gcd r y y.-1); rewrite -{1} yn gcdnC -{1} addn1 gcdnDl. 
  rewrite gcdn1 e1 e2 {2 3} /dvdn !modnMr eqxx /= dvdn1 => /eqP r1.
  move: e1 e2 e3; rewrite r1 !mul1n => e1 e2 e3.
  have /DE2_solution: (DE_eq2 p q). 
    rewrite /DE_eq2 - e2 -yn e1 [in RHS] addnS.
    by rewrite addn1 subnKC //  leq_exp2r ? hb.
  case; first by move => [pz]; move: yp; rewrite e2 pz.
  by move => [n [he hf]]; exists n; rewrite e3 he hf - fib_doubleS.
+ have oy: odd y.-1 = false.  
    by move: (f_equal odd e2); rewrite -doubleMr odd_double.
  have g2: r = 2.
    rewrite /r -{2} yn - (odd_double_half y.-1) oy add0n.
    rewrite -!muln2 - muln_gcdl (muln2 y.-1./2) -addnn  - addSn.
    by rewrite gcdnDr gcdnC (eqP (coprimeSn y.-1./2)).
  set p1 := p + q; set q1 := p - q.
  have pv: p.*2 = p1 + q1 by rewrite -addnn -{2} (subnKC hb) addnA.
  have qv: q.*2 = p1 - q1 by rewrite subnBA// - addnA addKn addnn.
  move/eqP: e1; rewrite g2 mul2n eqn_double subn_sqr => /eqP e1.
  move/eqP: e2; rewrite - eqSS yn g2 doubleMr qv mulnA mul2n pv mulnC.
  rewrite -subn_sqr e1 -/p1 -/q1 mulnC => /eqP e2.
  have: DE_eq2 p1 q1.
    by rewrite /DE_eq2 e2 -(addn1 (_ - _)) addnA subnKC // leq_exp2r // leq_BD.
  case/(DE2_solution).
     by move => [/eqP]; rewrite /p1 /q1 addn_eq0 => /andP[/eqP -> /eqP ->].
  move=> [n [p1v p2v]]; exists n; rewrite p1v p2v; split => //.
  apply/eqP; rewrite - eqn_double -!mul2n e3 g2 mulnA -[2 *2]/(2^2). 
  rewrite mulnDr -!expnMn ! mul2n pv qv p1v p2v - fibSS (fibSS n.*2) addKn.
  by rewrite fib_square_n3_n.
Qed.

End  DiophanteEquation.



Section Diophantine2.
Import GRing.Theory Num.Theory.
Local Open Scope ring_scope.

Definition DE_eq5 (x y:int):= (x^+2 + x*y + x - y^+2 == 0).
Definition DE_eq6 (x y:int):= (x^+2 - x*y - x - y^+2 == 0).


Lemma DE_eq6_sol n (x := fib n.*2.+1) (y := fib n.*2)(z := fib n.*2.+2):
  [/\  (x ^ 2)^2 = (x ^ 2)*(y * x) + (x ^ 2) + (y * x)^2,
       (y ^ 2)^2 + (y ^ 2)*(y * x) + (y ^ 2) = (y * x)^2,
       (x ^ 2)^2 + (x ^ 2)*(z * x) = (x ^ 2) + (z * x)^2 &
       (z ^ 2)^2 + (z ^ 2) = (z ^ 2)*(z * x) +  (z * x)^2] %N.
Proof.
split.
+ rewrite (mulnC y) expnMn -mulnSr -mulnDr addnC - (addn1 (x* y)%N) addnA.
  by rewrite -(DE1_sol n) mulnn.
+ rewrite -addnA  -mulnSr -mulnn -mulnDr expnMn.
  by rewrite (mulnC y) - (addn1 (x* y)%N) (DE1_sol n) addnA.
+ by rewrite -mulnn -mulnDr - (DE2_sol n) mulnDr muln1 addnC mulnC expnMn.
+ by rewrite -mulnn -mulnSr expnMn -mulnDr (addnC (z*x)%N) -DE2_sol addn1.
Qed.

Lemma DE_equiv_56 x y: (DE_eq5 x y) = (DE_eq6 (-x) y).
Proof. by rewrite /DE_eq5 /DE_eq6 sqrrN opprK mulNr opprK. Qed.

Lemma DE_eq6_alt x y: 
   (DE_eq6 x y) = ((x*+2 - (y+1))^+2 == (y+1)^+2 + (y*+2)^+2).
Proof.
rewrite sqrrB mulrnAl - mulrnA !exprMn_n  addrC - subr_eq0 opprD addrACA subrr.
rewrite add0r -mulNrn  -mulrnDl -mulNrn  -mulrnDl mulrn_eq0 /= mulrDr mulr1.
by rewrite opprD !addrA.
Qed.


Lemma DE_eq6_pos x y: 0 <= y -> DE_eq6 x y -> 
  exists n, y = (fib n.*2 * fib n.*2.+1)%N /\ 
     (x = (fib n.*2.+1 ^ 2)%N \/ x = -((fib n.*2 ^ 2)%N:int)).
Proof.
rewrite DE_eq6_alt => sa /eqP.
set z := (x *+ 2 - (y + 1)) => sb.
have eq1: y = `|y|%N by move: sa; case y.
have eq2: z ^+2 =  ((`|z|)^2)%N.
   by rewrite - abszX; move: (sqr_ge0 z); case: (z^+2).
have: DE_eq3 `|y| `|z|.
  move: sb; rewrite eq2 eq1 /DE_eq3 - PoszD addnn mulnn mulnn addn1. 
  by case => <-. 
move/DE_eq3_solution => [n [ha hb]]; exists n.
  rewrite eq1 ha; split => //.
have eq3: z = `|z|%:Z \/  z = - (`|z|%:Z) .
  by case: (z) => a; [left |right ].
have: x *+ 2  = z + (y+1) by rewrite /z subrK.
have h u: (u.*2)%:Z = (u%:Z) *+ 2 by rewrite -muln2 PoszM - mulr_natr.
case: eq3 => ->; rewrite hb eq1 ha - PoszD fib_doubleS mulnC.
  rewrite  - addnA (addnA (fib n.*2 ^ 2)%N) -(DE1_sol n).
  by move/eqP;rewrite addnn h eqr_muln2r /= => /eqP; left.
move => hw; right; apply/eqP;move: (DE1_sol n) hw.
rewrite -[X in _ *+2 = X] opprK opprD opprK - addnA addn1 => ->.
by move/eqP; rewrite addnAC addnn PoszD addrK h -mulNrn eqr_muln2r.
Qed.

Lemma DE_eq6_neg x y: y <0 -> DE_eq6 x y -> 
  exists n, y = -((fib n.*2.+2 * fib n.*2.+1)%N:int) /\ 
     (x = (fib n.*2.+1 ^ 2)%N \/ x = -((fib n.*2.+2 ^ 2)%N:int)).
Proof.
rewrite DE_eq6_alt => sa /eqP.
set z := (x *+ 2 - (y + 1)) => eq0.
have eq2: z ^+2 =  ((`|z|)^2)%N.
   by rewrite - abszX; move: (sqr_ge0 z); case: (z^+2).
have eq1: -y = `|y|%N by move: sa; case y.
have eq3 : (`|y|%:Z - 1) = (`|y|.-1)%N. 
  by move: sa;  clear;case: y => //; case.
have yp : 0 < `|y| by move: sa; case y.
have: DE_eq4 `|y| `|z|.
  move: eq0; rewrite eq2 - sqrrN - (sqrrN (y *+ 2)) opprD -mulNrn.
  by rewrite  eq1 eq3 - PoszD addnn mulnn mulnn; case => /eqP.
move/(DE_eq4_solution _ yp) => [n [ha hb]]; exists n; split.
  by apply: oppr_inj; rewrite opprK eq1 ha.
have eq4: z = `|z|%:Z \/  z = - (`|z|%:Z) by case: (z) => a; [left |right ].
have h u: (u.*2)%:Z = (u%:Z) *+ 2 by rewrite -muln2 PoszM - mulr_natr.
have: x *+ 2  = z +1 + (-(-y)) by rewrite opprK addrAC -addrA /z subrK.
case: eq4 => ->; rewrite hb -doubleS fib_doubleS eq1 ha.
  rewrite - (PoszD _ 1%N) addnAC (DE2_sol n) addnAC PoszD addrK addnn.
  by move/eqP; rewrite h eqr_muln2r /= => /eqP; left.
move => hw; right; apply/eqP; move /eqP: hw.
rewrite addrAC -opprD - PoszD - addnA -(DE2_sol n) addnA addnn PoszD opprD.
by rewrite addrK h -mulNrn eqr_muln2r.
Qed.


Lemma DE_eq6_solution (x y:int): (x^+2 - x*y - x - y^+2 == 0) <-> exists n,
  [\/ y = (fib n.*2 * fib n.*2.+1)%N /\ x = (fib n.*2.+1 ^ 2)%N,
      y = (fib n.*2 * fib n.*2.+1)%N /\ x = -((fib n.*2 ^ 2)%N:int),
    y = -((fib n.*2.+2 * fib n.*2.+1)%N:int) /\ x = (fib n.*2.+1 ^ 2)%N |
    y = -((fib n.*2.+2 * fib n.*2.+1)%N:int) /\ x = -((fib n.*2.+2^2)%N:int)
  ].
Proof.
split.
  move => h.
  case: (lerP 0 y) => yp.
    move: (DE_eq6_pos yp h) => [n [ha hb]]; exists n. 
    by case: hb; [ constructor 1 | constructor 2].
  move: (DE_eq6_neg yp h) => [n [ha hb]]; exists n. 
  by case: hb; [ constructor 3 | constructor 4].
have hu (a:nat): (a%:Z)^+2 = (a^2)%:Z by [].
rewrite /DE_eq6; move => [n]; move: (DE_eq6_sol n) => [ea eb ec ed].
case; move => [-> ->].
+ rewrite addrAC - addrA addrAC addrA hu ea PoszD hu addrK PoszD addrK.
  by rewrite PoszM subrr.  
+ by rewrite - mulNr opprK sqrrN ! hu -PoszM -PoszD eb subrr.
+ by rewrite sqrrN -mulrN opprK ! hu -PoszM -PoszD ec addnC PoszD addrK subrr.
+ rewrite !sqrrN mulrN !opprK mulNr - addrA addrACA - opprD !hu.
  by rewrite - PoszM -PoszD ed -PoszD subrr.
Qed.

End Diophantine2.

Lemma fib_plus_fib a b c: b <= c -> 
  (fib a == fib b + fib c) =
  [ || (b == 0) && (fib a == fib c), 
      [&& b ==c, (c==1) || (c== 2) & a==3],
      [&& b ==1, c==3 & a==4] | 
      (c==b.+1) && (a==b.+2)].
Proof.
case:b. 
  move => _.
  case wa: ((c == 1) && (a == 2)); first by move/andP:wa => [/eqP -> /eqP ->].
  by case wb: (0==c); rewrite - ? (eqP wb) /= orbF. 
move => b; rewrite/= !eqSS;case:b. 
  rewrite add1n - (addn1 (fib c)) (eq_sym 1 c) /=.
  case: c => // c _; rewrite !eqSS.
  case cz: (c==0); first by rewrite (eqP cz) (fib_eq a 3) /= !andbF !orbF.
  case co: (c==1); first by rewrite (eqP co) (fib_eq a 3) /= !andbF !orbF.
  case ct: (c==2); first by rewrite (eqP ct) (fib_eq a 4) /= ! andbF!orbF.
  simpl; apply/negP => /eqP ha.
  case: (ltnP c.+1 a) => lac; last first.
    by move: (fib_monotone lac); rewrite ha addn1 ltnn.
  have w: (3 <= c) by rewrite ltn_neqAle eq_sym ct ltn_neqAle eq_sym co lt0n cz.
  move: (fib_monotone  lac); rewrite ha fibSS leq_add2l => la.
  by move: (leq_trans (fib_monotone w) la).
move => b; rewrite leq_eqVlt; case/orP => ha.
  have hh:=(ltn_eqF (ltnSn b)).
  rewrite - (eqP ha) !eqSS eqxx hh /= orbF.
  case bz: (b==0); first  by rewrite (eqP bz)  (fib_eq a 3) !andbF !orbF.
  simpl; apply/negP => hb.
  case: (ltngtP b.+3 a) => lac.
  + move: (fib_monotone lac); rewrite (eqP hb) fibSS leq_add2r.
    by apply/negP;rewrite -ltnNge fib_smonotone_bis.
  + rewrite ltnS in lac; move: (fib_monotone lac).
    by rewrite (eqP hb) leqNgt ltn_paddr // fib_gt0.
  + by move: hb; rewrite - lac fibSS eqn_add2l fib_eq // !eqSS bz hh /= andbF.
rewrite (ltn_eqF ha) /=; move: ha; rewrite leq_eqVlt; case/orP=> ha.
  by rewrite - (eqP ha) addnC -fibSS eqxx fib_eq !eqSS !andbF!orbF.
have cp:=(ltn_predK ha).
rewrite (gtn_eqF ha) /=; apply/negP => hb.
case: (ltngtP a c.+1) => lac.
+ rewrite ltnS in lac; move: (fib_monotone lac). 
  by rewrite leqNgt (eqP hb) ltn_paddl // fib_gt0.
+ move:(fib_monotone lac); rewrite (eqP hb) fibSS leq_add2r leqNgt.
  by rewrite fib_smonotone //  !ltnS (ltnW(ltnW ha)) andbT.
+ move: hb; rewrite lac -cp fibSS addnC eqn_add2r fib_eq !eqSS  andbF orbF. 
  rewrite -eqSS -(eqSS _ 1) !cp (gtn_eqF ha) /= => /andP [h1 h2].
  by move: ha; rewrite (eqP h1) (eqP h2).
Qed.

Lemma lucas_plus_lucas a b c: b <= c -> 
  (lucas a == lucas b + lucas c) =
     [ || [&& a==3, b==0 & c==0], [&& a==0, b==1 & c==1] |
        (c==b.+1) && (a==b.+2)].
Proof.
have Ha i: i != 1 -> 2 <= lucas i.
  by case: i => [| [| i _]]//; apply: ltnW; apply: (@lucas_monotone 2 i.+2).
have Hb i: 2 <=i -> 3 <= lucas i by apply:(lucas_monotone (m:=2)).
case az: (a== 0). 
  rewrite (eqP az) !andbF /= orbF => lbc; case: (ltngtP 1 b) => b1.
  +  apply/negP => /eqP h.
    by move: (Hb _ b1); rewrite -(ltn_add2r (lucas c)) - h.
  + move: b1; rewrite ltnS leqn0 => /eqP ->.
    by rewrite -{1} (addn0 (lucas 0)) eqn_add2l /= (ltn_eqF (lucas_gt0 c)).
  + by rewrite - b1 /= -[lucas 0]/(1+(lucas 1))  eqn_add2l lucas_injective_bis.
case bz: (b == 0).
  rewrite (eqP bz) /= => _.
  case cz: (c== 0).
     rewrite (eqP cz) /= andbT orbF; exact: (lucas_injective_bis a 3).
  case co: (c== 1).
     rewrite (eqP co) andbF /=; exact: (lucas_injective_bis a 2).
  rewrite andbF /=; apply/negP => /eqP h.
  case:(ltnP c a) => ha; last first.
    have /lucas_monotone: 0 < a <=c by rewrite ha lt0n az.
    by rewrite h ltnNge leqnSn.
  have /lucas_monotone ww : 0 < c.+1 <= a by rewrite ha.
  have /prednK cp : O < c by rewrite lt0n cz.
  move: ww; rewrite  h -{1}cp lucasSS addnC cp leq_add2r  lucas_monotoneE.
  rewrite !andbF /= -!(eqSS c.-1) cp co /= andbT orbF => c2.
  move: h; rewrite (eqP c2); clear;case: a => [|[|[|[| a]]]] // ea.
  have /lucas_monotone :0 < 4 <= a.+4 by []. 
  by rewrite ea.
rewrite /= andbF /=.
rewrite leq_eqVlt; case/orP => ebc.
  rewrite - (eqP ebc) (ltn_eqF (ltnSn b)) /=; apply/negP => /eqP h.
  case: (ltngtP b.+1 a) => lab.
  + have /lucas_smonotone ha: 0 < b < b.+1 by rewrite ltnSn lt0n bz.
    have /lucas_monotone: 0 < b.+2 <= a by rewrite lab. 
    by rewrite lucasSS h leq_add2r leqNgt ha.
  + have /lucas_monotone: 0 < a <= b by rewrite lt0n - ltnS lab az.
    by rewrite h  -{3} (add0n (lucas b)) leq_add2r leqNgt lucas_gt0.
  + move /eqP:h; rewrite -lab.
    move:bz; clear; case: b => // b _.
    by rewrite lucasSS eqn_add2l lucas_injective_bis; apply/negP /eqP.
apply/eqP/andP; last by move => [/eqP -> /eqP ->]; rewrite lucasSS addnC.
move => h.
have c1:= (ltn_predK ebc).
have /lucas_monotone: 0 < b <= c.-1 by  rewrite lt0n bz - ltnS c1 ebc.
rewrite - (leq_add2r (lucas c)) -h addnC - {1} c1 -lucasSS c1 => lb.
case: (ltngtP a c.+1) => la.
+ have /lucas_monotone: 0 < a <= c by rewrite lt0n az -ltnS la.
  by rewrite h -{2}(add0n (lucas c)) leq_add2r leqNgt lucas_gt0.
+ have /lucas_smonotone: 0 < c.+1 < a by rewrite la.
  by rewrite ltnNge lb.
+ move /eqP: h; rewrite la - c1 lucasSS addnC eqn_add2r lucas_injective_bis.
  by move/eqP ->. 
Qed.

Lemma fib_eq_lucas m n: (fib m == lucas n) = 
  [|| (n==0) &&(m==3), (n==1) &&((m==1) || (m==2))  | (n==2)&&(m==4) ].
Proof.
case nz: (n==0).
   by rewrite (eqP nz) lucas0 (fib_eq m 3) !andbF.
have ha:= (leq_ltn_trans (leq_pred n) (ltnSn n)).
rewrite lucas_fib ? nz // addnC (fib_plus_fib _ (ltnW ha)) (ltn_eqF ha) !eqSS.
have hc:=(prednK (neq0_lt0n nz)).
case no: (n==1); first by rewrite (eqP no) /= fib_eq andbF !orbF andbT orbC.
case nt: (n==2); first by rewrite (eqP nt) /= orbF.
by rewrite - eqSS hc no andbF /= - {1} hc  (gtn_eqF (ltnSn n.-1)).
Qed.

Lemma lucas_times_fib_is_fib m n k:
   (fib n == lucas k * fib m) =
   [|| [&& k==0, n==3 & (m==1) || (m==2) ],
       (k==1) && [|| n == m, (n == 1) && (m == 2) | (n == 2) && (m == 1)] ,
       ( ((m==0) && (n == 0))
         || [&& ((m==1) || (m==2)), (k==2) &(n==4) ]) |
       (k==m) && (n == m.*2)].
Proof.
case mz: (m==0). 
  by rewrite (eqP mz) muln0 fib_eq0; case nz:(n== 0); rewrite ?orbT //= !andbF.
case m12: ((m == 1) || (m == 2)).
  have ->: fib m = 1 by case/orP:m12 => /eqP ->.
  rewrite muln1 fib_eq_lucas andbT /=; case:((k == 0) && (n == 3)) => //=.
  case n1: (n ==1). 
    rewrite (eqP n1) andbT andbF /= !orbF (eq_sym 1 m) m12 andbT.
    by case:(orP m12) => /eqP ->; rewrite andbF orbF.
  case n4: (n ==4). 
    rewrite /= (eqP n4) andbT !andbF /= orbF.
    by case:(orP m12) => /eqP ->; rewrite !andbF ?orbF // andbT/= orbb.
  rewrite andbF /= orbF;case:(orP m12)=> /eqP ->. 
    by rewrite n1 /= andbT orbb. 
  by rewrite n4 !andbF !orbF.
have [ha hb]: (m==1) = false /\ (m==2) = false by move: m12; case: eqP.
rewrite !andbF /=; case kz: (k==0). 
  rewrite (eqP kz) lucas0 mul2n -addnn fib_plus_fib //= (eq_sym 0 m).
  by rewrite mz /= m12 /= andbF ha (ltn_eqF (ltnSn m)).
case k1: (k==1).
  by rewrite (eqP k1) mul1n fib_eq (eq_sym 1) ha hb /= !andbF !orbF.
have mk5: (5 <= m + k).
  have k2: 2 <= k by rewrite ltn_neqAle lt0n eq_sym k1 kz.
  have m3: 3 <= m by rewrite ltn_neqAle ltn_neqAle lt0n eq_sym hb eq_sym mz ha.
  exact: (leq_add m3 k2).
move: (gtn_eqF mk5)  (gtn_eqF (ltnW mk5)) (ltnW(ltnW mk5))=> mk4 mk3 mk5'.
move: (gtn_eqF mk5') (gtn_eqF (ltnW mk5')) => mk2 mk1.
have Hw p: p.*2 ==1 = false by case:p.
have LTD m' k': (k' == 0) = false -> m' - k' < m' + k'.
  move => k'z; apply:(leq_ltn_trans (leq_subr k' m')). 
  by rewrite ltn_paddr // lt0n k'z.
case: (ltngtP m k) => hc; last first.
+ rewrite hc mulnC - fib_double_lucas fib_eq -[2]/(1.*2) eqn_double k1.
  by rewrite Hw  !andbF !orbF.
+ rewrite (fib_lucas1 (ltnW hc)) /=; apply/negP => /eqP.
  have hd:= (LTD m k kz). 
  case: odd; last first.
    move/eqP;rewrite addnC (fib_plus_fib _ (ltnW hd)) subn_eq0  leqNgt mk3 mk2.
    rewrite hc (ltn_eqF hd) /= - [in m +k](subnK (ltnW hc)) - addnA addnn.
    by rewrite andbF /= - addn1 eqn_add2l Hw.
  move: (subnK (ltnW hc)) => he ea.
  move/eqP :(esym (subnK (fib_monotone (ltnW hd)))); rewrite - ea.
  case /orP: (leq_total n (m - k)) => cnmk; [ | rewrite (addnC (fib n))  ];
    rewrite (fib_plus_fib _ cnmk) mk4 mk3 !andbF /=.
     case/orP; first by rewrite fib_eq (gtn_eqF hd) /= mk1 mk2 /= andbF.
    rewrite - {2} he - addnA addnn => /andP[/eqP ->] /eqP  h.
    by move:(f_equal odd h); rewrite odd_add odd_double addbF /=;case:odd.
  rewrite subn_eq0 leqNgt hc /= - {2} he => /andP[_].
  by rewrite -addnA -addn2 eqn_add2l addnn (eqn_double _ 1) k1.
+ rewrite (fib_lucas2 (ltnW hc)) ;  apply/negP => /eqP.
  have he:= (subnKC (ltnW hc)).
  move: (LTD k m mz); rewrite addnC => hd.
  case: odd.
    move/eqP; rewrite addnC (fib_plus_fib _ (ltnW hd)) subn_eq0 mk1 mk2 mk3.
    by rewrite !andbF leqNgt hc //= -{1} he addnA addnn -add1n eqn_add2r Hw.
  move => ea.
  have: fib (m + k) == fib n + fib (k - m).
    by rewrite ea; rewrite subnK // (fib_monotone (ltnW hd)).
  case /orP: (leq_total n (k - m)) => cnmk;[ | rewrite (addnC (fib n))  ];
     rewrite (fib_plus_fib _ cnmk) mk4 mk3 !andbF /=.
     case/orP; first by  rewrite fib_eq (gtn_eqF hd) /= mk1 mk2 /= andbF.
     rewrite - {2} he addnA addnn => /andP[/eqP ->] /eqP  h.
     by move:(f_equal odd h); rewrite odd_add odd_double /=;case:odd.
   rewrite subn_eq0 leqNgt hc /= - {2} he => /andP[_].
   by rewrite addnA -add2n eqn_add2r addnn (eqn_double _ 1) ha.
Qed.


Lemma lucas_times_lucas_is_fib m n k: k <= m ->
   (fib n == (lucas m) * (lucas k)) =
    [|| [&& k==0, m == 1 & n == 3], [&& k==0, m == 3 & n == 6],
        (k==1) && 
         [|| (m == 1) && (n == 1), (m == 1) && (n == 2) | (m == 2) && (n == 4)]
        | [&& k ==2, m==4 & n==8] ].
Proof.
move => h.
case kz: (k == 0). 
  by rewrite (eqP kz) -[lucas 0]/(fib 3) lucas_times_fib_is_fib !andbF !orbF.
case kn1: (k == 1). 
  move:h;rewrite (eqP kn1) muln1 fib_eq_lucas /= lt0n; case: eqP => // _ _.
  by case m1: (m==1); rewrite orbF // (eqP m1) andFb !orbF.
have sk := (subnK h).
simpl;apply/eqP/idP; last by move/and3P => [/eqP -> /eqP -> /eqP ->].
have mkz: m + k != 0 by rewrite addn_eq0 kz andbF.
have la: 2 <= k by move: kz kn1; case:(k) => //; case.
have mk2:=(leq_add (leq_trans (ltnW la) h) (ltnW la)).
move:(subnK mk2); rewrite addn2 => hb.
rewrite (lucas_lucas1 h); case ok: (odd k); last first. 
  rewrite (lucas_fib mkz) => ea.
  have: fib (m + k).+1 < fib n.
    by rewrite ea -addnA -[X in X < _] addn0 ltn_add2l addn_gt0 lucas_gt0 orbT.
  move/fib_monotone_bis => /fib_monotone. 
  rewrite ea -addnA fibSS leq_add2l -hb fibSS leq_add2l.
  move:h; rewrite leq_eqVlt; case/orP => hc.
    move: ea;rewrite - (eqP hc) subnn lucas0 - ltnS -[3]/(fib 4) => fn h.
    move: (fib_monotone_bis h) fn kz ok; case k => //; case => //; case => //.
      rewrite -[RHS ]/9 => _ eb _ _; case: (ltngtP 7 n) => sa.
      + by move:(@fib_smonotone 7 n); rewrite eb sa /=; apply.
      + by rewrite ltnS in sa;move:(fib_monotone sa); rewrite eb.
      + by move: eb; rewrite - sa.
    by move => n1; rewrite !addnS !addSn /= subn2 !ltnS ltn0.
  move: (hc); rewrite - subn_gt0 => /gtn_eqF /negbT/lucas_lt_fib /leqifP.
  move:ea; rewrite - [in m+k] sk - !addnA addnn.
  case ha: (m-k==2). 
    rewrite -[in m==4] sk (eqP ha) addKn.
    move: kz ok; clear; case: k => [| [| [ | k ]]]//.
      move => _ _; rewrite -[RHS]/(fib 8) => /eqP. 
      by rewrite fib_eq !andbF !orbF. 
    move => _ _ _ _ h.
    have: 2 < (k.+2).*2 by rewrite !doubleS !ltnS.
    by move /fib_smonotone_bis; rewrite ltnNge h.
  move => ea lc lb; move:(leq_ltn_trans lb lc) => /fib_monotone_bis.
  move: kz ok; clear; case: k => [| [| k]] // _ _.
  by rewrite !doubleS -(addn2 k.*2.+2) addnA addnK - 2!addSnnS ltnNge leq_addr.
move:h;rewrite leq_eqVlt; case/orP => lkm.
  rewrite - (eqP lkm) subnn lucas0; move: ok kn1; clear; case:k => //k.
  rewrite addnS addSn addnn lucas_fib //=; case:k => // k ok _.
  have e2: 2 < fib (k.+1).*2.+1.  
     apply: (fib_monotone(m:=4)); rewrite doubleS !ltnS double_gt0.
     by move:ok;case:(k).
  rewrite  -(addnBA _ (ltnW e2)) => eq1.
  have: fib (k.+1).*2.+3 < fib n.
    by rewrite eq1 -[X in X < _] addn0 ltn_add2l subn_gt0.
  move/fib_monotone_bis => /fib_monotone; rewrite fibSS eq1 leq_add2l fibSS.
  by rewrite -{1} (subnK (ltnW e2)) -addnA leqNgt add2n addnS ltnS leq_addr.
move => ea.
have mkgt4:=(leq_add (leq_ltn_trans la lkm) la).
have eb: fib n + lucas (m - k) = lucas (m + k).
  rewrite ea subnK // lucas_monotone // subn_gt0 lkm /=; apply: leq_BD.
move /leqifP: (lucas_lt_fib mkz).
rewrite eq_sym (ltn_eqF (ltnW(ltnW mkgt4))) - eb => bnd1.
move:(leq_ltn_trans (leq_addr (lucas (m - k)) (fib n)) bnd1).
move => /fib_monotone_bis; rewrite ltnS => /fib_monotone.
rewrite -(leq_add2r (lucas (m - k))) eb (lucas_fib mkz) leq_add2l => bnd2.
move:lkm; rewrite leq_eqVlt; case/orP => lkm1.
   move: bnd2; rewrite - (eqP lkm1)  subSnn addSn addnn /=.
   have: 1 < 3 < k.*2 by move: kz kn1; clear; case:k => [|[|]]//.
   by move /fib_smonotone => hu hv; move:(leq_trans (ltnW hu) hv).
move:lkm1; rewrite leq_eqVlt; case/orP => lkm2.
  move: bnd2; rewrite - (eqP lkm2) - (add2n k) addnK -addnA addnn add2n.
  rewrite -[lucas 2]/(fib 4) leqNgt fib_smonotone //= ltnS (leq_double 2 k).
  by move: kz kn1; clear; case:k => [|[|]]//.
move:(lkm2);rewrite - addn2 addSn -ltn_subRL => wa.
move/leqifP: (lucas_lt_fib (negbT (gtn_eqF (ltnW(ltnW wa))))).
rewrite (gtn_eqF wa) => wb.
move:(fib_monotone_bis (leq_ltn_trans bnd2 wb)).
rewrite ltnNge - {2} sk -addnA addnn - {3} (ltn_predK la) doubleS !addnS.
rewrite !ltnS -{1} (addn0 (m-k)) ltn_add2l double_gt0.
by move:kz kn1;clear; case: k => [| [| ]].
Qed. 

Lemma fib_times_c_is_fib1 n k c: k !=1 -> k != 2 ->
    fib n = c * (fib k) -> k %| n.
Proof.
move => k1 k2 h.
move:(gcd_fib n k); rewrite h gcdnC gcdnMl => /esym /eqP.
by rewrite fib_eq (negbTE k1) (negbTE k2) !andbF !orbF => /eqP /gcdn_idPr.
Qed.

Lemma fib_times_c_is_fib2 n k c: 2 <= c -> 2 < k -> 
    fib n = c * (fib k) -> (lucas k) <= c.
Proof.
move => ha hb hc.
have fkz:(fib k == 0) = false.
   by rewrite fib_eq0 eqn0Ngt (ltnW (ltnW hb)).
case k1:(k==1); first by  move:hb; rewrite (eqP k1).
case k2:(k==2); first by  move:hb; rewrite (eqP k2).
move:(fib_times_c_is_fib1 (negbT k1) (negbT k2) hc) => /dvdnP [a nv].
move: hc; rewrite nv => /eqP.
case: (ltngtP a 1).
+ rewrite ltnS leqn0 => /eqP ->.
  by rewrite  eq_sym muln_eq0 fkz eqn0Ngt (ltnW ha).
+ move => sa sb.
  have: 2 *k <= a * k by  rewrite leq_mul2r sa orbT.
  move/fib_monotone; rewrite mul2n fib_double_lucas (eqP sb) mulnC.
  by rewrite leq_mul2r fkz.
+ by move ->; rewrite mul1n - {1}(mul1n (fib k)) eqn_mul2r fkz (ltn_eqF ha).
Qed.

Lemma fib_times_c_is_fib3 n k : 
  fib n == 2 * (fib k) = ((k==0) && (n==0)) || ((n==3) && ((k==1) || (k==2))).
Proof.
rewrite (lucas_times_fib_is_fib k n 0) andbF !orbF /= (eq_sym 0 k).
by case kz: (k==0); rewrite ? orbF // (eqP kz) !andbF orbb orbF.
Qed.

Lemma fib_times_c_is_fib4 n k : 
  fib n == 3 * (fib k) = ((k==0) && (n==0)) || (((k==1) || (k==2)) &&(n==4)).
Proof.
rewrite (lucas_times_fib_is_fib k n 2) /= (eq_sym 2 k).
by case kz: (k==2); rewrite ? orbF //= (eqP kz) orbb.
Qed.

Lemma fib_times_c_is_fib5 n k m: 2 < k -> 2 < m ->
  fib n <> fib m * fib k.
Proof.
wlog: k m / k <= m.
  case /orP:(leq_total k m) => // ha hb. by apply: hb.
  by move => hc h; rewrite mulnC; apply: hb.
move => sb sa _ h.
have m3 := (leq_trans sa sb).
have ms:= (ltn_predK  m3).
have ha: m.+1 != 0 by [].
have hb: m != 0 by rewrite -ms.
have hc: 0 < m.-1 by rewrite - ltnS ms (ltnW m3).
have fmp: (0 < fib m) by rewrite fib_gt0 // lt0n.
have lmn: m < n.
  apply/fib_monotone_bis; rewrite h -{1} (muln1 (fib m)) ltn_mul2l.
  rewrite fmp; apply:(fib_monotone sa). 
move:(fib_add (n-m) hb); rewrite  (subnKC (ltnW lmn)) => eq1.
have : fib m * fib (n - m).+1 < fib n.
  by rewrite eq1 ltn_paddl // muln_gt0 !fib_gt0 ?subn_gt0.
rewrite h ltn_mul2l fmp /= => /fib_monotone_bis => la.
have: fib m.-1 * fib (n - m) <  fib m * fib (n - m).
  by rewrite ltn_mul2r fib_gt0 ?subn_gt0 //= fib_smonotone // -ltnS ms m3 leqnn.
rewrite -(leq_add2r (fib m * fib (n - m).+1)) addSn - eq1 -mulnDr addnC.
rewrite - fibSS h ltn_mul2l fmp // => /fib_monotone_bis; rewrite ltnS.
by rewrite leqNgt la.
Qed.


Lemma fib_times_lucas_is_lucas n k m: 
  lucas n == (fib m) * (lucas k) = 
  [ || ((m==1) || (m==2)) && (n == k),
    ((k==1) &&
    [|| (n==0) &&(m==3), (n==1) &&((m==1) || (m==2))  | (n==2)&&(m==4) ])
  | [&& k ==0 , n == 3 & m ==3] ].
Proof.
have sc: (n == k) = false -> false = (k == 1) && (n == 1).
  by case k1: (k==1) => //;rewrite (eqP k1). 
case mz:(m==0).
  by rewrite (eqP mz) mul0n (gtn_eqF (lucas_gt0 n)) !andbF /=.
case m1: (m==1). 
  rewrite (eqP m1) /= mul1n lucas_injective_bis; case nk: (n == k) => //.
  by rewrite !andbF andbT /= !orbF; apply: sc.
case m2: (m==2).
  rewrite (eqP m2) /= mul1n lucas_injective_bis; case nk: (n == k) => //.
  by rewrite !andbF andbT /= !orbF; apply: sc.
case k1: (k==1). 
  by rewrite (eqP k1) muln1 eq_sym fib_eq_lucas m1 m2 !andbF /= orbF.
have lt1: 1 < m by move: mz m1; case m => [|[]].
have lt2: 2 < m by move: mz m1 m2; case m => [|[|[]]].
have ms1p:  0 < m.-1 by move: mz m1; case m => [|[]].
have ww := (ltn_predK lt1).
case kz: (k==0).
  rewrite (eqP kz) lucas0 /=; case m3:(m==3).
    by rewrite (eqP m3) -[fib 3 * 2]/ (lucas 3) lucas_injective_bis andbT.
  rewrite andbF; apply /negbTE/eqP => eqa.
  move:(lucas_ge_2fib lt1); rewrite - muln2 -eqa => eqb.
  case: (ltnP m n) => lmn.
    have /lucas_smonotone :0 < m < n by rewrite (ltnW lt1) lmn.
    by rewrite ltnNge eqb.
  case nz: (n==0).
    move:(leq_mul2r 2 (fib 3) (fib m)); simpl; rewrite (fib_monotone lt2) - eqa.
    by rewrite (eqP nz) lucas0. 
  case nt: (n==2).
     move: eqa; rewrite (eqP nt) muln2 => h; move:(f_equal odd h).
     by rewrite odd_double.
  have: fib m.+1 <= lucas n.
    by rewrite eqa muln2 -addnn -ww fibSS leq_add2l fib_monotone.
  move/leqifP:(lucas_lt_fib (negbT nz)); rewrite nt => ha hb.
  move:(leq_ltn_trans hb ha) => /fib_monotone_bis; rewrite !ltnS => hc.
  move: (eqn_leq m n); rewrite lmn hc /= => /eqP emn.
  move:eqa; rewrite - emn  muln2 -addnn (lucas_fib (negbT mz)) - {1}ww.
  move/eqP; rewrite fibSS ww -addnA eqn_add2l eq_sym addnn - mul2n.
  by rewrite fib_times_c_is_fib3 mz -3!(eqSS m.-1) ww m1 m2 m3.
simpl;  apply/negP => /eqP h.
have fp:= (fib_gt0 (ltnW lt1)).
have lk3: 3 <= lucas k. 
  by rewrite(lucas_monotoneE 2) /= orbF -leq_eqVlt ltn_neqAle eq_sym lt0n kz k1.
have  la: m < n.
  have b1 := (leq_mul (fib_monotone lt2) lk3).
  case nz: (n== 0); first by move: b1; rewrite - h (eqP nz).
  case n2: (n== 2); first by move: b1; rewrite - h (eqP n2).
  move/leqifP:(lucas_lt_fib (negbT nz)); rewrite n2 h.
  move: (ltnW lk3); rewrite - (leq_pmul2r fp) mul2n mulnC => sa sb.
  have lc : fib n.+2  <= (fib n.+1).*2. 
    by rewrite fibSS -addnn leq_add2l fib_monotone //.
  move: (leq_trans (leq_ltn_trans sa sb) lc); rewrite ltn_double.
  move/fib_monotone_bis; rewrite ltnS leq_eqVlt; case/orP => // emn.
  move: lk3; rewrite - (leq_pmul2l fp) - h (eqP emn). 
  move: nz n2; clear; case: n => //n _; rewrite lucas_fib // fibSS.
  rewrite mulnS -addnA leq_add2l /= muln2 addnn leq_double leqNgt.
  case: n => //; case => //n; rewrite fib_smonotone // !ltnS leqnn //.
move: (lucas_add m.-1 (n-m)); rewrite -addnS ww (subnK (ltnW la)) => eq2.
have: lucas (n - m).+1  * fib m < lucas n.
  rewrite eq2 ltn_paddr // muln_gt0 lucas_gt0 fib_gt0 //. 
rewrite h mulnC ltn_mul2l fp /= => lb.
case: (ltnP (n - m).+1 k) => lc; last first.
   by move: lb; rewrite ltnNge lucas_monotone //lc lt0n kz.
have:lucas (n - m) * fib m.-1 < lucas (n - m) * fib m.
  by rewrite ltn_mul2l lucas_gt0 /= fib_smonotone // - ltnS ww lt2 leqnn.
rewrite -(ltn_add2l (lucas (n - m).+1 * fib m)) -eq2 h -mulnDl -lucasSS.
by rewrite mulnC ltn_mul2r fp /= ltnNge lucas_monotone.
Qed.


Lemma lucas_times_lucas_is_lucas m n k: k <= m -> 
  lucas n == (lucas m) * (lucas k) = 
  [ || [&& k ==0, m == 0 & n == 3],
       [&& k ==0, m == 1 & n == 0] |
       [&& k ==1 & m == n] ].
Proof.
move => km.
case kz: (k==0).
  rewrite mulnC (eqP kz) -[lucas 0]/(fib 3) fib_times_lucas_is_lucas.
  by rewrite /= ! andbF !orbF eqxx !andbT orbC.
case k1: (k==1).
  by rewrite mulnC (eqP k1) lucas1 mul1n /= lucas_injective_bis.
simpl;  apply/negP => /eqP; rewrite lucas_lucas1 //.
have ha: 1 < k by rewrite ltn_neqAle lt0n kz eq_sym k1.
have hb:=(leq_add (leq_trans  ha km) ha).
have x0:= (gtn_eqF(ltnW (ltnW(ltnW hb)))).
have x1 :=(gtn_eqF (ltnW(ltnW hb))).
case ok: (odd k); last first.
  move/eqP; rewrite addnC lucas_plus_lucas ? leq_BD //  x0 x1 !andbF /=.
  rewrite -{1} (subnKC km) addnAC addnn - add1n eqn_add2r.
  by move/andP => [/eqP ea _]; move:(f_equal odd ea); rewrite odd_double.
case: (ltnP (lucas (m + k)) (lucas (m - k))) => hh.
  by rewrite (eqP (ltnW hh))=> h; move: (lucas_gt0 n); rewrite h.
move => hc.
have: lucas (m + k) == lucas (m - k) + lucas n.
 by rewrite - {1} (subnK hh) - hc addnC.
case /orP: (leq_total (m - k) n) => la.
  rewrite lucas_plus_lucas // (gtn_eqF  hb) x0 /= => /andP[_].
  by rewrite - {1} (subnK km) -addnA -addn2 eqn_add2l addnn (eqn_double k 1) k1.
rewrite (addnC (lucas _)) lucas_plus_lucas // (gtn_eqF  hb) x0 /= => /andP[].
move/eqP => <- /eqP ea; move:(f_equal odd ea).
by rewrite -{1} (subnK km) -addnA addnn odd_add /= odd_double addbF; case:odd.
Qed.

Lemma fib_times_fib_is_lucas m n k: k <= m -> 
  lucas n == (fib m) * (fib k) = 
  [|| (m==3) && [|| (k==1) && (n==0), (k==2) && (n==0) | (k==3) && (n==3)],
    (k==1) && [|| (n==1)&&(m==1), (n==1) &&(m==2) | (n==2) && (m==4) ] |
    (k==2) && [|| (n==1) &&(m==2) | (n==2) && (m==4) ] ].
Proof.
set H := lucas_injective_bis.
case m3:(m==3).
   rewrite (eqP m3) mulnC (fib_times_lucas_is_lucas n  0 k) /= !andbF !orbF.
   by rewrite orbA - andb_orl (andbC (k == 3)).
case k1: (k == 1).
  rewrite /= (eqP k1) muln1 eq_sym (fib_eq_lucas) /=.
  case n0: (n==0); first by rewrite (eqP n0) /= m3.
  by case n1: (n==1); rewrite orbF //  (eqP n1) /= !orbF.
case k2: (k == 2).
  rewrite /= (eqP k2) muln1 eq_sym (fib_eq_lucas) m3 /= => /gtn_eqF ->.
  by rewrite andbF.
move => le1 /=;apply/negP => h.
case:(ltnP k 4) => k4.
  move: k4;rewrite leq_eqVlt eqSS; case /orP => k4.
    move: le1 h; rewrite (eqP k4) (fib_times_lucas_is_lucas n  0 m) => m2.
    by rewrite m3 (gtn_eqF m2) (gtn_eqF (ltnW m2)) /= andbF.
  move: k4; rewrite !ltnS leq_eqVlt k2 ltnS leq_eqVlt k1 ltnS leqn0 /= =>/eqP.
  by move => kz; move: (gtn_eqF (lucas_gt0 n)); rewrite (eqP h) kz muln0.
move: (f_equal (muln 5) (eqP h));rewrite mulnA lucas_lucas2 // => h1.
have la: m < m + k  by rewrite -{1} (addn0 m) ltn_add2l (ltnW (ltnW(ltnW k4))).
have bnd1:= (leq_add (leq_trans (ltnW k4) le1) k4).
have bnd2 :=(subnK (ltnW(ltnW bnd1))).
set q := (m + k - 5) in bnd2.
move:(lucas5S q); rewrite bnd2 => ea.
have eb: lucas (m - k) <= lucas q. 
   case emk: (k==m). 
     rewrite -(eqP emk) subnn; apply: ltnW; apply:(@lucas_monotone 2).
     by rewrite /= -(leq_add2r 5) bnd2 bnd1.
  have mp:=(ltn_predK (leq_trans k4 le1)).
  have mp1: m - k <= m.-1 by rewrite -(leq_add2r k) (subnK le1) -ltnS -addSn mp.
  apply: lucas_monotone;rewrite subn_gt0 ltn_neqAle emk le1 (leq_trans mp1) //.
  by rewrite  -(leq_add2r 5) bnd2 -addSnnS mp leq_add2l.
have: lucas (m - k) < 2 * lucas q. 
  by apply: (leq_ltn_trans eb); rewrite -[X in X< _] mul1n ltn_mul2r lucas_gt0.
rewrite - (ltn_add2l (lucas (m + k))) => sa.
have sb: 5 * lucas n <= (lucas (m + k)) + (lucas (m - k)).
  rewrite h1; case: odd => //; apply: leq_BD.
move: (leq_ltn_trans sb sa); rewrite ea - addnA -mulnDl - mulnDr - lucasSS.
rewrite ltn_mul2l /= => e1.
case: (ltnP q.+1 n) => e3.
   have: 0 < q.+2 <= n by [].
   by move/lucas_monotone; rewrite leqNgt e1.
have ec:  (lucas (m + k)) - (lucas (m - k)) <=  5 * lucas n.
  rewrite h1; case: odd => //; apply: leq_BD.
have: 0 < (2 * lucas q + (lucas q - lucas (m - k))).
  move:(lucas_gt0 q); rewrite - double_gt0 - mul2n => pa.
  apply: (leq_trans pa); apply: leq_addr.
move:(addnBA (5 * lucas q.+1 + 2 * lucas q)  eb).
rewrite - 2!addnA -mulSnr - ea  -(ltn_add2l (5* lucas q.+1)) addn0.
move => -> ed; move: (leq_trans ed ec); rewrite ltn_mul2l /= ltnNge => /negP.
case; case: (posnP n) => np; last by apply: lucas_monotone; rewrite np e3.
have: 0 < 3 <= q.+1 by rewrite /= -ltnS ltnS ltnS -(leq_add2r 5) bnd2.
by move/lucas_monotone; apply: leq_trans; rewrite np.
Qed.


Lemma fib_sum_square_is_fib_square m n k: 
   0 < m <= n -> (fib m)^2  + (fib n)^2 = (fib k)^2 -> False.
Proof.
move => /andP [la lb] hb.
case: (ltnP n k) => cp; last first.
  move:(fib_monotone cp);  rewrite leqNgt => /negP; case.
  by rewrite -ltn_sqr -(add0n (fib n ^ 2)) -hb ltn_add2r sqrn_gt0 fib_gt0.
move:(fib_monotone cp); rewrite -(leq_pmul2l (m:=2)) // => sa.
case: (ltngtP 1 n).
+ move/fib_mon1 => sb;  move:(leq_trans sb sa); rewrite leqNgt => /negP.
  case;rewrite -ltn_sqr !expnMn - hb -[3^2]/(5 + 2^2) mulnDr mulnDl ltn_add2r.
  apply: (@leq_ltn_trans (4 * fib n ^ 2)).
    by rewrite leq_pmul2l // leq_sqr fib_monotone.
  by rewrite ltn_pmul2r // expn_gt0 fib_gt0 // (leq_trans la lb).
+ by rewrite ltnNge (leq_trans la lb).
+ move => n1; move: hb; rewrite -n1; move /square_plus1_square => fz.
  by move: (fib_gt0 la); rewrite fz.
Qed.

Lemma lucas_sum_square_is_lucas_square m n k: 
   m <= n -> (lucas m)^2  + (lucas n)^2 = (lucas k)^2 -> False.
Proof.
move => la hb.
case kz: (k==0).
   case n1: (n == 1). 
       by move:la hb; rewrite (eqP kz)(eqP n1); case:m => [|[|]].
   have lb: 1 <= lucas m ^ 2  by rewrite (ltn_sqr 0) lucas_gt0.
   have lc: 4 <= lucas n ^ 2.  
      move:n1;rewrite (leq_sqr 2); case: (n) => [|[|u _]] //.
      by apply: ltnW;apply: (@lucas_monotone 2).
  by move: (leq_add lb lc); rewrite hb (eqP kz).
case: (ltnP n k) => cp; last first.
  have: 0 < k <= n by rewrite lt0n kz cp.
  move/lucas_monotone; rewrite leqNgt => /negP; case.
  by rewrite -ltn_sqr -(add0n (lucas n ^ 2)) -hb ltn_add2r sqrn_gt0 lucas_gt0.
have HH x: 8<  x.+3 ^ 2 by rewrite (leq_sqr 3 x.+3) //.
have Ha x : x ^2 = 5 -> False.
   by case: x => [|[|[|x h]]] //; move: (HH x); rewrite  h.
have Hb x : x ^2 = 8 -> False.
   by case: x => [|[|[|x h]]] //; move: (HH x); rewrite  h.
case: (ltnP 2 n); last first.
  rewrite leq_eqVlt ltnS  leq_eqVlt ltnS leqn0; case/or3P => n1.
  + move: la hb; rewrite (eqP n1);rewrite leq_eqVlt ltnS  leq_eqVlt ltnS leqn0.
    case/or3P => m1.
    - by rewrite (eqP m1) addnn => /double_square_square.
    - by rewrite (eqP m1) addnC => /square_plus1_square.
    - rewrite (eqP m1) -[LHS]/13; case: (k) => [|[|[|x h]]] //.
      suff // : 0 < 3<=x.+3 by  move/lucas_monotone; rewrite -leq_sqr -h. 
  +  move: hb; rewrite (eqP n1); move/square_plus1_square => lz.
     by move:(lucas_gt0 m); rewrite lz.
  +  by move: la hb; rewrite (eqP n1) leqn0 => /eqP -> /esym /Hb.
move /lucas_mon1 => sb.
have: 0 < n.+1 <= k by rewrite cp.
move/lucas_monotone; rewrite -(leq_pmul2l (m:=2)) // => sa.
move:(leq_trans sb sa); rewrite leqNgt => /negP; case.
rewrite -ltn_sqr !expnMn - hb -[3^2]/(5 + 2^2) mulnDr mulnDl ltn_add2r.
case mz: (m==0).
  move: hb; rewrite (eqP mz);  case:(n) =>[| [| n1]].
  + by move/esym/Hb.
  + by move/esym/Ha.
  + move => _; apply: (@leq_trans 45) => //;rewrite (@leq_pmul2l 5 9) //.
    by rewrite (leq_sqr 3); apply:(@lucas_monotone 2).
apply: (@leq_ltn_trans (4 * lucas n ^ 2)).
  by rewrite leq_pmul2l // leq_sqr lucas_monotone // la lt0n mz.
by rewrite ltn_pmul2r // expn_gt0 lucas_gt0.
Qed.

Lemma lucas_lucas_fib_square m n k: m <= n ->
  ((lucas m)^2 + (lucas n^2) == (fib k)^2) = [&& m==2, n==3 & k==5].
Proof.
have H x: lucas x = 0 -> False.
   by move/eqP;rewrite (gtn_eqF(lucas_gt0 x)).
move => lemn; apply/eqP/idP; last first.
  by move =>/and3P [/eqP -> /eqP -> /eqP ->].
move:lemn;rewrite leq_eqVlt; case/orP => lmn.
  by rewrite (eqP lmn) addnn => /double_square_square => /H.
case m0: (m==0).
  by rewrite (eqP m0) addnC => /square_plus4_square /H.
case m1: (m==1).
   by rewrite (eqP m1) addnC => /square_plus1_square /H.
have m2: 2 <= m by move: m0 m1; clear; case:m => [|[]].
have la: 3 <= lucas m by apply: (@lucas_monotone 2).
have lb: 4 <= lucas n. 
    by apply: (@lucas_monotone 3); rewrite /=(leq_ltn_trans m2 lmn).
have lc: 25 <= lucas m ^ 2 + lucas n ^ 2.
  move: la; rewrite - leq_sqr => la.
  move: lb; rewrite - leq_sqr => lb.
  by rewrite (leq_add la lb).
move => h; have ld: 5 <= (fib k) by rewrite -leq_sqr - h.
move: h ld; case:k => [|[|[| [| [|]]]]] //; case.
  case lm2: (m==2).
    rewrite (eqP lm2) => /eqP.
    rewrite -[fib 5 ^ 2]/(lucas 2 ^ 2 + lucas 3 ^ 2) eqn_add2l.
    by rewrite eqn_sqr lucas_injective_bis => ->.
  have m3: 0 < 3 <= m by rewrite /= ltn_neqAle eq_sym lm2 m2.
  have: 0 < 4 <= n by rewrite /= (leq_trans  _ lmn).
  move/lucas_monotone ; rewrite -leq_sqr => ha.
  move:(lucas_monotone m3); rewrite -leq_sqr => hb h. 
  by move:(leq_add hb ha); rewrite h.
have Ha a b: a <= a - b + b.
   case /orP: (leq_total a b) => lab; last  by rewrite subnK.
    move:(lab); rewrite {1} /leq; move => /eqP ->//.
move => k.
have ->: k.+2.+4 = k+6 by rewrite !addnS addn0.
have l05: 0 < 5 by [].
have l5_12: 5 <= 12 by [].
move:(lucas5S (k.*2+7)); rewrite -(addnA _ 7 5) -[7 + 5]/12 => Lk h _.
set x := 5*( (lucas m.*2 + lucas n.*2)).
have: (x <= lucas (k.*2+12) + 22) && (lucas (k.*2+12) <= x + 22).
  move /eqP: h; rewrite -(eqn_pmul2l l05).
  rewrite !lucas_square mulnA lucas_lucas2 ?leqnn // addnn subnn lucas0.
  have ->: odd (k + 6) = ~~(odd k.+1) by rewrite odd_add addbF/=; case: odd.
  pose T b x := (if b then subn else addn) x 2.
  have Ta: forall b x, x <= (T b x)  + 2. 
     by rewrite /T;move => b y; case b => //; rewrite -addnA leq_addr.
  have Tb: forall b x, (T b x) <= x + 2. 
      rewrite /T;move => b y; case b => //; apply: leq_BD.
  rewrite doubleD if_neg => /eqP ha; apply/andP; split.
     move:(Tb (odd k.+1)  (lucas(k.*2 + 12))); rewrite -(leq_add2r 20) - addnA.
     move: (leq_add (Ta (odd m)  (lucas m.*2)) (Ta (odd n)  (lucas n.*2))).
     rewrite addnACA; rewrite - (leq_pmul2l l05) (mulnDr _ _ 4) ha -/x.
     apply: leq_trans.
   apply: (leq_trans(Ta (odd k.+1)  (lucas(k.*2 + 12)))).
   rewrite (addnA _ 20 2) leq_add2r /T -ha /x - (mulnDr 5 _ 4) leq_pmul2l //.
   rewrite -[4]/(2 +2) addnACA; apply: leq_add; apply: Tb.
move /andP => [ha hb].
have le: lucas (k.*2+12) +22 < 5* lucas (k.*2 +9).
   rewrite Lk (addnS k.*2 8) (addnS k.*2 7).
   rewrite lucasSS - addnA mulnDr ltn_add2l(mulnDl 3 2) ltn_add2l mul2n.
   rewrite (ltn_double 11); apply: (@lucas_smonotone 5); rewrite l05 //=.
   by rewrite -addSnnS -{1} (add0n 6) leq_add2r.
have hc: 5 * lucas n.*2 <= x by rewrite /x mulnDr leq_addl.
move: (leq_ltn_trans (leq_trans hc ha) le); rewrite ltn_pmul2l //.
case: (ltngtP (k.*2 +8)  n.*2 ) => hd.
    by rewrite ltnNge; move/negP; case; apply: lucas_monotone;rewrite addnS hd. 
  have he: x + 22 <= 5 * (lucas n.*2.+1) + 22.
    move: lmn; rewrite - ltn_double => sa.
    have hx:= (ltn_predK sa). 
    rewrite leq_add2r /x (leq_pmul2l l05) -{2}hx lucasSS addnC hx leq_add2l. 
    by apply: lucas_monotone; rewrite (ltn_double 0) lt0n m0 - ltnS hx //.
  have : 22 <3 * lucas (k.*2 +7). 
    apply: ltnW; rewrite (@leq_pmul2l 3 8) => //; apply: (@lucas_smonotone 4).
    by rewrite /= (addnA _ 2 5) leq_addl.
  rewrite - (ltn_add2l (5 * lucas n.*2.+1)) => hf.
  move: (leq_ltn_trans (leq_trans hb he) hf).
  rewrite Lk ltn_add2r (ltn_pmul2l l05) ltnNge => /negP; case.
  by apply:lucas_monotone; rewrite - addnS hd.
move /eqP: hd; rewrite -(doubleD k 4) eqn_double eq_sym => /eqP hd _.
move:ha hb; rewrite /x Lk hd doubleD mulnDr addnC (addnS k.*2  7) - 2!addnA.
rewrite !leq_add2l (addnS k.*2 6) (addnS k.*2 5) lucasSS (addnS k.*2 4) lucasSS.
rewrite addnAC addnn -(mul2n (lucas _)) mulnDr mulnA => ec ed.
set u := lucas (k.*2 + 4).+1 + 3 * lucas (k.*2 + 4).
have : 22 < u. 
   apply: (@leq_trans (lucas 5 + 3 * (lucas 4))) => //.
   by apply: leq_add; rewrite ?(@leq_pmul2l 3)-? addnS  //;
       apply: (lucas_monotone); rewrite /= leq_addl.
rewrite -(ltn_add2l (5 * lucas m.*2)) => ef.
move:(leq_ltn_trans ed ef); rewrite (mulSnr 5) - addnA ltn_add2r ltn_pmul2l //.
move => ww. 
case: (ltngtP (k.*2 + 4).+2 (m.*2)) => eg.
+ have: 0 < (k.*2 + 4).+3 <= m.*2 by rewrite eg.
  move/lucas_monotone; rewrite -(leq_pmul2l l05) => sa.
  move:(leq_trans sa ec); rewrite lucasSS mulnDr (mulSnr 5) - 2!addnA. 
  rewrite addnC leq_add2l lucasSS mulnDr (addnC _ 22) (mulSn 4) - addnA.
  rewrite leq_add2l (mulnDl 2 3) addnA leq_add2r.
  have: 0 < 4 <= (k.*2 + 4).+1 by rewrite /= -addSn leq_addl.
  move/lucas_monotone;rewrite -(@leq_pmul2l 4) // => sb sc. 
  have sd: 22 < 4* lucas 4 by [].
  move: (leq_trans (leq_ltn_trans sc sd) sb).
  rewrite ltnNge; move/negP; case; apply: leq_addr.
+ move: ww; rewrite ltnNge => /negP; case; apply: lucas_monotone. 
  by rewrite - (ltnS m.*2)  eg double_gt0 lt0n m0.
+ move:ec; rewrite - eg  lucasSS mulnDr (mulSnr 5) - 2!addnA leq_add2l.
  rewrite (addnC _ 22) addnA (mulnDl 2 3) leq_add2r addnS lucasSS mul2n - addnn.
  rewrite - addnA leq_add2l addnS lucasSS leq_add2l.
  move: eg; rewrite -!addnS -(doubleD k 3) =>/eqP; rewrite eqn_double =>/eqP ha.
  have L1: lucas 1 = 1 by rewrite lucas1.
  have L2: lucas 2 = 3 by [].
  have L3: lucas 3 = 4 by rewrite lucasSS.
  have L4: lucas 4 = 7 by rewrite lucasSS L3 L2.
  have L5: lucas 5 = 11 by rewrite lucasSS L4 L3.
  have L6: lucas 6 = 18 by rewrite lucasSS L5 L4.
  have L7: lucas 7 = 29 by rewrite lucasSS L6 L5.
  have F5: fib 5 = 5 by [].
  have F6: fib 6 = 8 by rewrite fibSS F5.
  have F7: fib 7 = 13 by rewrite fibSS F6 F5.
  have F8: fib 8 = 21 by rewrite fibSS F6 F7.
  move: h; rewrite hd - ha; case k => [|[ | [| k']]];
     rewrite ? L3 ? L4 ? L5 ? L6 ? F5 ? F6 ? F7 ? F8 //.
  have: 0 < 8 <= ((k'.+3).*2 + 2) by rewrite /= addn2 !doubleS //.
  move/lucas_monotone => sa _ sb.
  by move: (leq_trans sa sb); rewrite lucasSS L7 L6.
Qed.

Lemma fib_sum_square_is_fib_square_bis m n k: 
  (fib m)^2  + (fib n)^2 == (fib k)^2 =
    ((m==0) && (fib n== fib k)) || ((n == 0) && (fib m== fib k)).
Proof.
wlog: m n / m <= n.
   move => H; case/orP:(leq_total m n); first by apply: H.
   by move => h; rewrite addnC orbC; apply: H.
move => mn; case: (posnP m) => mp.
 by  rewrite mp add0n eqn_sqr; case: (posnP n) => np; rewrite ?orbF//?np ?orbb.
rewrite (gtn_eqF (leq_trans mp mn)) /=. 
by apply/eqP /fib_sum_square_is_fib_square; rewrite mn mp.
Qed.


Lemma lucas_fib_lucas_square m n k:
  ((fib m)^2 + (lucas n^2) == (fib k)^2) =
    ((m==0) && (fib k == lucas n)) || [&& k ==5, m==4 & n==3].
Proof.
case :(posnP m) => mz; first by rewrite mz eqn_sqr eq_sym /= !andbF orbF.
have fmp:=(fib_gt0 mz).
have fm: ~(fib m = 0) by move => h; move: fmp; rewrite h.
case:n => [|[|[| [|n]]]].
+ by rewrite /= !andbF; apply/negP => /eqP /square_plus4_square.
+ by rewrite /= !andbF; apply/negP => /eqP /square_plus1_square.
+ rewrite -[lucas 2]/(fib 4).
  by rewrite (fib_sum_square_is_fib_square_bis) (gtn_eqF mz) !andbF.
  rewrite -[lucas 3 ^ 2]/(4 ^2) square_plus16_square (gtn_eqF fmp)  /=.
+ by rewrite (fib_eq m 4) (fib_eq k 5) /= !andbF !orbF andbT andbC.
+ rewrite !andbF /=; apply/negP => /eqP.
have ln :  ~(lucas n.+4 = 0) by move => h; move: (lucas_gt0 n.+4);rewrite h.
case: (ltngtP (fib m) (lucas n.+4)); last first.
    by move => ->; rewrite addnn; move/double_square_square.
  move => sa sb. 
  case: (ltnP m k) => ha.
    move: (mz); rewrite leq_eqVlt; case/orP => m2.
        by move: sb; rewrite addnC - (eqP m2); move /square_plus1_square.
    move:(fib_mon1 m2); rewrite - leq_sqr !expnMn => h.
    move: (fib_monotone ha); rewrite - leq_sqr => sc.
    have: (lucas n.+4) ^2 < (fib m)^2 by rewrite ltn_sqr sa.
    rewrite -(ltn_add2l (fib m ^ 2)) sb addnn - mul2n => sd.
    move: (leq_ltn_trans sc sd); rewrite -(@ltn_pmul2l 4) // mulnA => hc.
    by move:(leq_ltn_trans h hc); rewrite (ltn_pmul2r) // sqrn_gt0.
  move: (fib_monotone ha); rewrite -leq_sqr - sb leqNgt => /negP; case.
  by rewrite -{1} (addn0 (fib m ^ 2)) ltn_add2l sqrn_gt0 lucas_gt0.
move => sa sb; case: (ltngtP k (n.+4.+2))=> kn4. 
+ have hh: lucas n.+4 < fib k. 
    by rewrite  -ltn_sqr -(add0n  (lucas n.+4 ^ 2)) - sb ltn_add2r  sqrn_gt0.
  rewrite ltnS in kn4; move: (leq_trans hh (fib_monotone kn4)).
  by rewrite lucas_fib //= -{2} (addn0 (fib n.+4.+1)) ltn_add2l ltn0.
+ move:(fib_monotone kn4); rewrite fib3S -leq_sqr.
  move: sa; rewrite -ltn_sqr -(ltn_add2r (lucas n.+4 ^ 2)) sb addnn => sc sd.
  move: (leq_ltn_trans sd sc); rewrite ltnNge => /negP; case.
  rewrite sqrnD lucas_fib //= sqrnD 2!doubleD - 2!addnA -(muln2 (fib n.+4.+1)). 
  have: (fib n.+4.+1 ^ 2).*2 + (fib n.+3 ^ 2).*2  <= (fib n.+4.+1 * 2) ^ 2. 
    rewrite expnMn - doubleD  (mulnA _ 2 2) muln2 muln2 leq_double - addnn.
    by rewrite leq_add2l leq_sqr fib_monotone // ltnS; apply: ltnW; apply: ltnW.
  rewrite -(@leq_add2r (fib n.+4 ^ 2 + 2 * (fib n.+4.+1 * 2 * fib n.+4))) => ww.
  apply:leq_trans ww; rewrite - addnA leq_add2l leq_add2l (mulnC _ 2) -mul2n. 
  apply: (@leq_trans (2 * (2 * (fib n.+4.+1 * fib n.+4)))).
    by rewrite !leq_pmul2l //? fib_gt0 // fib_monotone.
  by rewrite - mulnA leq_addl.
move /eqP: sb; rewrite kn4 lucas_fib //= fib3S (fib3S n.+3) addnAC - addnA.
rewrite -fibSS - !mul2n 2!sqrnD  2!expnMn mulnAC addnA eqn_add2r addnA.
rewrite (mulSnr 3) (mulSn 3) - (addnA (fib n.+4 ^ 2)) addnC  eqn_add2l.
rewrite addnA eqn_add2r => sx.
have sc: 3 * (fib n.+3)^2 < 2 *(fib n.+4)^2.
  have ww: 1 < n.+3 by [].   
  move:(fib_mon1 ww); rewrite - (@leq_pmul2r (fib n.+3)) ? fib_gt0 // => h.
  rewrite - mulnn - mulnn 2!mulnA; apply: (leq_ltn_trans h).
  by rewrite (ltn_pmul2l) // ?fib_smonotone //= muln_gt0 fib_gt0.
have sb: 3 * fib n.+4 ^ 2 < (fib n.+4.+2)^2.
  rewrite (fibSS (n.+4))  (fibSS (n.+3)) addnAC addnn sqrnD - addnA.
  rewrite -mul2n expnMn (mulSnr 3) -addnA -[X in X < _] (addn0) ltn_add2l.
  by rewrite addn_gt0 sqrn_gt0 fib_gt0.
case: (ltngtP m n.+4.+1).
+ rewrite ltnS; move/fib_monotone; rewrite leqNgt - ltn_sqr.
  by rewrite -(ltn_add2r (2 * fib n.+4 ^ 2)) - mulSn - (eqP sx) ltn_add2l sc.
+ move/fib_monotone; rewrite -leq_sqr => sd.
  by move:(leq_trans sb sd); rewrite - (eqP sx) ltnNge leq_addr.
+ move => eq1.
  move: sx; rewrite (fib_square_succ n.+2) addnC mulnDr eqn_add2l eq1.
  rewrite -mulnn mulnA eqn_pmul2r ? fib_gt0 // fib4S - {2}(addn0 (3 *_)).
  rewrite eqn_add2l double_eq0 fib_eq0 //.
Qed.


(** Properties of ordered sequences *)

Definition ggen := [rel m n | m >= n.+2].
Definition llen := [rel n m | ggen m n]. 
Definition even := [pred n | ~~ (odd n) ].

Lemma sorted_gtn l: uniq l -> sorted gtn (rev (sort leq l)).
Proof.
rewrite rev_sorted ltn_sorted_uniq_leq sort_uniq (sort_sorted leq_total) => ->.
done.
Qed.

Lemma transitive_llen:  transitive llen.
Proof. by move => x y z /= sa /ltnW sb; exact: (ltn_trans sa sb). Qed.

Lemma irreflexive_llen: irreflexive llen.
Proof. by move => x /=;  rewrite ltnNge leqnSn. Qed.

Lemma sorted_ggenW s : sorted ggen s -> sorted gtn s.
Proof.
by case: s => //= n s; elim: s n => //= m s IHs n /andP [/ltnW -> /IHs].
Qed.

Lemma sorted_ggenS s : all even s -> sorted gtn s -> sorted ggen s.
Proof.
case: s => // n s; elim: s n => //= m s Ihs n /andP [on ha] /andP [lnm hb].
rewrite Ihs //; case/andP:ha => /negbTE => om _; move: lnm.
by rewrite (evenE(negbTE on)) (evenE om) - doubleS leq_double ltn_double andbT.
Qed.

Lemma sorted_llen_uniq l: sorted llen l -> uniq l.
Proof.
apply: (sorted_uniq transitive_llen irreflexive_llen).
Qed.

Lemma sorted_ggen_uniq l : sorted ggen l -> uniq l.
Proof. 
by rewrite - {2} (revK l) - rev_sorted rev_uniq; apply: sorted_llen_uniq.
Qed.

Lemma uniq_llen a l: sorted llen (a :: l) -> uniq l.
Proof. by move/path_sorted => /sorted_llen_uniq. Qed.


Lemma path_all_llen a l: path llen a l -> all (llen a) l.
Proof. by apply: (order_path_min transitive_llen). Qed.

Lemma sorted_ggen_succ l: sorted ggen (succ_seq l) = sorted ggen l.
Proof.
by case: l => //= a l; elim: l a => // a l H b /=; rewrite ltnS H.
Qed.

Lemma sorted_llen_succ l: sorted llen (succ_seq l) = sorted llen l.
Proof.
by case: l => //= a l; elim: l a => // a l H b /=; rewrite ltnS H.
Qed.

Lemma mkseq_uniq (f: nat -> nat) a n: 
  injective f -> uniq [seq (f i) | i <- iota a n].
Proof. move => h; rewrite (map_inj_uniq h); exact: iota_uniq.  Qed.

Lemma sorted_llen_mkseq f a n: (forall u, llen (f u) (f u.+1)) ->
  sorted llen [seq (f i) | i <- iota a n].
Proof.
move => h; case: n => // n /=; elim: n a => // n Hrec a /=. 
rewrite (Hrec a.+1) andbT; exact: (h a). 
Qed.

Lemma sorted_llen_mkseq_e a n: sorted llen [seq i.*2 | i <- iota a n].
Proof. by apply:sorted_llen_mkseq => u /=; rewrite doubleS !ltnS. Qed.

Lemma sorted_ggen_sdouble n: sorted ggen (rev (mkseq double n)).
Proof. by rewrite rev_sorted; apply:sorted_llen_mkseq_e. Qed.

Lemma sorted_ge2_all_ps l: sorted ggen (rcons l 0) ->
   all (leq 2) l /\ all (leq 1) l.
Proof.
rewrite - rev_sorted rev_rcons; move/path_all_llen; rewrite all_rev => h.
by split; apply/allP => [x /(allP h) //= /ltnW].
Qed.

(**  Definition of [Zeck_val ] etc *)
Definition Zeck_val l := \sum_(i <-l) fib (i.+2).
Definition Zeck_valp l := \sum_(i <-l) fib (i.+1).
Definition Zeck_valpp l := \sum_(i <-l) fib i.

Lemma Zeckv_nil : Zeck_val nil = 0.
Proof. by rewrite /Zeck_val big_nil. Qed.

Lemma Zeckv_cons n l: Zeck_val (n ::l) = fib (n.+2) + Zeck_val l.
Proof. by rewrite /Zeck_val big_cons. Qed.

Lemma Zeckvp_cons n l: Zeck_valp (n ::l) = fib (n.+1) + Zeck_valp l.
Proof. by rewrite /Zeck_valp big_cons. Qed.

Lemma Zeckv_rev l: Zeck_val (rev l) = Zeck_val l.
Proof. by rewrite /Zeck_val sum_rev. Qed.

Lemma Zeckvp_rev l: Zeck_valp (rev l) = Zeck_valp l.
Proof. by rewrite /Zeck_valp sum_rev. Qed.

Lemma Zeck_valppE l: Zeck_val l = Zeck_valp l +  Zeck_valpp l. 
Proof.
rewrite /Zeck_val/Zeck_valp/Zeck_valpp. 
by elim:l => [| a l H]; rewrite ?big_nil // !big_cons addnACA fibSS H.
Qed.

Lemma Zeckv_pos n l: 0 < Zeck_val (n ::l).
Proof. by rewrite Zeckv_cons addn_gt0 fib_gt0. Qed.

Lemma Zeckv_bound0 n l : path gtn n l -> (Zeck_val (n::l)).+2 <= fib (n.+4).
Proof.
elim: l n => [n _ | a l Hrec /= n/andP []].
  rewrite Zeckv_cons Zeckv_nil - addnS - addnS (fibSS n.+2) addnC.
  by rewrite leq_add2r (@fib_monotone 3).
rewrite - 3!ltnS => /fib_monotone la /Hrec lb. 
by rewrite fibSS addnC Zeckv_cons -addnS ltn_add2l (leq_trans lb la).
Qed.

Lemma Zeckv_bound1 n l : path gtn n l -> Zeck_val (n::l) < fib (n.+4).
Proof. by move/Zeckv_bound0 => /ltnW. Qed.

Lemma Zeckv_bound2 n l : path ggen n l -> Zeck_val (n::l) < fib (n.+3).
Proof.
elim: l n => [n _ |  a l Hrec /= n/andP []].
  by rewrite Zeckv_cons Zeckv_nil addn0 fib_smonotone_bis.
rewrite - ltnS  => /fib_monotone la /Hrec lb.
by rewrite fibSS Zeckv_cons ltn_add2l (leq_trans lb la).
Qed.

Lemma Zeckv_bound3 l n: uniq l -> (all (leq^~ n) l) -> 
    (Zeck_val l).+2 <= fib n.+4.
Proof.
move /sorted_gtn;set l' := (rev (sort leq l))  => sa /allP sb.
have hc: perm_eq l l'.
  rewrite /l' perm_eq_sym; apply:(@perm_eq_trans _  (sort leq l)).
    by elim:(sort leq l)=> // a s h; rewrite rev_cons perm_rcons perm_cons.
 by apply/perm_eqlP; apply: perm_sort.
have ->: (Zeck_val l) = (Zeck_val l') by apply: eq_big_perm.
have:(all (leq^~ n) l').
  apply/allP => x; rewrite -(perm_eq_mem hc x); apply: sb.
move: sa; case l'. 
  by move => _ _; rewrite Zeckv_nil  -[1]/(fib 2) //; apply:fib_smonotone_bis. 
move => a s pa pb; apply: (leq_trans (Zeckv_bound0 pa)).
by apply: fib_monotone; rewrite !ltnS; apply/(allP pb); rewrite inE eqxx.
Qed.

Lemma Zeck2_unique (s s': seq nat) : sorted ggen s -> sorted ggen s' -> 
   Zeck_val s = Zeck_val s' ->  s = s'.
Proof.
have A a l: Zeck_val [::] = Zeck_val (a :: l) -> False.
  by rewrite Zeckv_nil => h; move: (Zeckv_pos a l); rewrite - h.
elim: s' s; first by  case => // a l _ _; move/ esym /A.
move => a l Hrec; case; first by move => _ _ /A.
move => a' l'; rewrite !Zeckv_cons => pa pb ec.
suff aux:(a' == a).
  move /eqP: ec; rewrite (eqP aux) eqn_add2l => /eqP h.
  by rewrite (Hrec l'  (path_sorted pa) (path_sorted pb) h).
move:(Zeckv_bound2 pa); rewrite Zeckv_cons ec.
move/ (leq_ltn_trans (leq_addr (Zeck_val l) (fib a.+2))) => /fib_monotone_bis.
move:(Zeckv_bound2 pb); rewrite Zeckv_cons -ec.
move/ (leq_ltn_trans (leq_addr (Zeck_val l') (fib a'.+2))) => /fib_monotone_bis.
by rewrite !ltnS eqn_leq => -> ->.
Qed.

Definition odd_last l := if l is a::b then odd(last a b)  else 2.

Lemma Zeck_valp_aux l: sorted gtn l ->
  exists (l': seq nat), 
  [/\ sorted ggen l', odd_last l = odd_last l',
    Zeck_val l = Zeck_val l', Zeck_valp l = Zeck_valp l' &
     size l' <= size l ?= iff (sorted ggen l)].
Proof.
have Hb a s: Zeck_valp (a::s) = fib (a.+1) + Zeck_valp s. 
  by rewrite /Zeck_valp big_cons.
pose z l := (Zeck_val l, Zeck_valp l, odd_last l).
have He a l1 : z [:: a.+1, a & l1] = z (a.+2 :: l1).
  have od: odd (last a.+2 l1)= odd (last a l1) by case: l1 => //=;case: odd.
  by rewrite /z !Zeckv_cons !Hb addnA addnA - !fibSS /= od.
have Hf a l1 l2: z l1 = z l2 -> z (a :: l1) = z (a::l2).
  rewrite /z !Zeckv_cons !Hb; case => eq1 eq2 eq3; rewrite eq1 eq2 /=.
  suff: odd (last a l1) = odd (last a l2) by move => ->.
  move: eq1 eq3; clear; case: l1; case: l2 => //.
  + by move => u v h;move:(Zeckv_pos u v); rewrite -h Zeckv_nil.
  + by move => u v h;move:(Zeckv_pos u v); rewrite h Zeckv_nil.
  + by move => u la v lb //= _; case:odd; case:odd.
suff H: forall (a:nat) l, sorted gtn (a :: l) ->
  exists (b:nat) s, [/\  sorted ggen (b::s), z(a::l) = z(b::s), b <= a.+1 &
  size s <= size l ?= iff sorted ggen (a::l) ].
  case: l => //; first by move => _; exists nil.
  by move => a l /H [b [s [pa  [pb  pc pd _] pf]]]; exists (b::s).
move =>  {l} a l.
move: {2} ((size l).+1) (ltnSn (size l))=> n; elim: n a l; first by case.
move => n Hrec a [_ _ | b l ]; first by exists a, nil. 
rewrite /= ltnS => lt1 /andP [lt2 pa].
move: lt2; rewrite leq_eqVlt; case /orP => [/eqP <- | lt3].
  move: l lt1 pa; case; first by exists (b.+2), nil; rewrite ltnn.
  move => c l /= pa /andP [pb pc].
  move: (Hrec c l (ltn_trans (ltnSn (size l)) pa) pc).
  move => [u [v [/= qa qb qc qd]]]; exists (b.+2), (u::v). 
  rewrite He (Hf b.+2 _ _ qb) /= qa ! ltnS (leq_trans qc pb) ltnn.
  by split => //; apply/leqifP; rewrite !ltnS /= qd.
case ww: (path ggen b l).
  by exists a, (b::l);rewrite /= lt3 ww; split => //; apply /leqif_refl.
move: (Hrec b l lt1 pa) => [c [l' [r1 /(Hf a _ _ ) -> r4]] sc].
move:(leq_ltn_trans r4 lt3); rewrite leq_eqVlt; case /orP => lt4; last first.
  by exists a, (c:: l'); rewrite /= lt4 lt3 /= -ww mono_leqif.
exists (a.+1), l'; rewrite  - (eqP lt4) He andbF.
move: sc; rewrite /sorted ww => /leqifP => /ltnW ss.
have K:size l' <= (size l).+1 ?= iff false by apply /leqifP; rewrite ltnS.
split => //; move: r1; case l' => // d l'' /= /andP[ w ->].
by rewrite (ltn_trans w (ltn_trans (ltnSn c) (ltnSn c.+1))).
Qed.

Lemma Zeck_valp_same (l1 l2: seq nat): sorted gtn l1 -> sorted gtn l2 ->
    Zeck_val l1 =  Zeck_val l2 ->  
    Zeck_valp l1 =  Zeck_valp l2 /\  odd_last l1 = odd_last l2. 
Proof.
move /Zeck_valp_aux => [l3 [pa -> -> -> _]] /Zeck_valp_aux [l4 [pb -> -> -> _]].
by move/(Zeck2_unique pa pb) ->.
Qed.

(** Existence of a representation *)


Fact fib_cont_aux1 n: exists i, fib i.+2 <= n.+1.
Proof. by exists 0. Qed.

Fact fib_cont_aux2 n i: fib i.+2 <= n.+1 -> i <= n.
Proof. by move /(leq_trans (fib_gen i.+1)); rewrite ltnS.  Qed.

Definition fib_content n := ex_maxn (fib_cont_aux1 n) (@fib_cont_aux2 n).

Lemma fib_contentP n (r := fib_content n):  fib r.+2 <= n.+1 < fib r.+3.
Proof.
rewrite /r /fib_content;case:ex_maxnP => i sa sb; rewrite sa  /=.
by case: (ltnP (n.+1) (fib i.+3)) => // /sb; rewrite ltnn.
Qed.

Lemma fib_content_lt n (r := fib_content n): n.+1 - fib r.+2 < fib r.+1.
Proof.
move :(fib_contentP n) => /andP; rewrite -/r; move => [/subnK -{1} <- ].
by rewrite (fibSS r.+1) addnC ltn_add2l.
Qed.

Lemma fib_content_large m: m.+1 - fib (fib_content m).+2 <= m.
Proof. by rewrite fib_pos subSS leq_subr. Qed.

Lemma fib_content_eq n: fib_content ((fib n.+2).-1) = n.
Proof.
move: (fib_contentP (fib n.+2).-1). 
rewrite /= - fib_pos  => /andP[sa /fib_monotone_bis].
rewrite !ltnS leq_eqVlt; case/orP; first by move/eqP. 
by move => /fib_smonotone_bis; rewrite ltnNge sa.
Qed.

(** The Zeckendorf function *)

Fixpoint Zeck_rec n k:=
   if k is k'.+1 then
     if n is n'.+1 then let r := fib_content n' in 
       r:: Zeck_rec (n - (fib (r.+2))) k'
    else nil
   else nil.
Definition Zeck n := Zeck_rec n n.


Lemma Zeck_0 : Zeck 0 = nil.
Proof. by []. Qed.

Lemma Zeck_S' n (r := fib_content n) : 
   Zeck n.+1 = r :: (Zeck (n.+1 - (fib (r.+2)))).
Proof.
have Ha := fib_content_large.
suff aux: forall m n k1 k2, m <= k1 -> m <= k2 ->  n <= m ->
    Zeck_rec n k1 = Zeck_rec n k2.
  by congr cons; apply: (aux (n.+1 - fib (fib_content n).+2)).
clear n r. 
elim; first by move => n k1 k2 _ _;rewrite leqn0 => /eqP ->; case: k1; case: k2.
move => m Hrec n; case => // k1; case => // k2; rewrite (leq_eqVlt n) ! ltnS.
move => mk1 mk2 /orP [ /eqP ->| lenm]; first by congr cons; apply:Hrec.
by apply:  Hrec => //; apply: ltnW; rewrite ltnS.
Qed.

Lemma Zeck_S k n: fib k.+2 <= n < fib k.+3 ->
  Zeck n = k :: Zeck (n - fib k.+2).
Proof.
case: n => [|n bd]; first by rewrite leqn0 fib_eq0.
move /eqP: (fib_partition (fib_contentP n) bd); rewrite eqSS eqSS Zeck_S'.
by move/eqP ->.
Qed.

Lemma Zeck_fib n: Zeck (fib n.+2) = [:: n].
Proof.
have eq1:= (fib_pos n.+1).
by rewrite eq1 Zeck_S' fib_content_eq - eq1 subnn Zeck_0.
Qed.

Lemma Zeck_1 : Zeck 1 = [:: 0].  Proof. exact: (Zeck_fib 0). Qed.
Lemma Zeck_2 : Zeck 2 = [:: 1].  Proof. exact: (Zeck_fib 1). Qed.

Lemma Zeck_ggen n: sorted ggen (Zeck n).
Proof.
elim: n {-2} n (leqnn n) => [ [] | n Hr k] //;rewrite leq_eqVlt ltnS.
case /orP => //; [move/eqP => -> | by apply: Hr].
move: (fib_content_lt n)(fib_content_large n); rewrite Zeck_S' /= => sa sb.
move:(Hr _ sb) sa; case: (_ - _) => // v; rewrite Zeck_S' /= => -> la.
move/andP: (fib_contentP v) => [lb _]; move: (leq_ltn_trans lb la).
by move/fib_monotone_bis; rewrite ltnS andbT.
Qed.

Lemma Zeck_uniq n: uniq (Zeck n).
Proof. exact: (sorted_ggen_uniq (Zeck_ggen n)).  Qed.

Lemma Zeck_zeck_val n: Zeck_val (Zeck n) = n.
Proof.
elim: n {-2} n (leqnn n).
  by move => n; rewrite leqn0 => /eqP ->; rewrite Zeck_0 Zeckv_nil.
move=> n IH n1; rewrite leq_eqVlt; case/orP=> [/eqP ->|Hn]; last first.
  by apply: IH; rewrite -ltnS.
rewrite Zeck_S' Zeckv_cons; move:(fib_content_large n) => h.
by rewrite (IH _ h); apply: subnKC; move/andP: (fib_contentP n) => [].
Qed.

Lemma ZeckP l: sorted ggen l -> Zeck (Zeck_val l) = l.
Proof.
move => h.
by apply: (Zeck2_unique (Zeck_ggen (Zeck_val l)) h); rewrite Zeck_zeck_val.
Qed.

Lemma Zeck_prop1 n: n != 0 -> exists a l, 
  [/\ sorted llen (a::l), Zeck n = rev (a::l) & n = Zeck_val (a::l) ].
Proof.
move:(Zeck_ggen n)(Zeck_zeck_val n); case: n => // n.
rewrite Zeck_S' - (revK (_ :: _)) /= rev_sorted split_rev.
set u := last _ _; set v := behead _ => ra rb _.
by exists u, v; split => //; rewrite - rb Zeckv_rev.
Qed.  

Lemma Zeck_is_minimal l n (L := Zeck n): 
   sorted gtn l -> Zeck_val l = n -> size L <= size l ?= iff (l == L).
Proof.
move => ha hb; apply /leqifP.
move: (Zeck_valp_aux ha) => [ s [ /ZeckP pa _ pc _]].
rewrite  -pa - pc hb -/L; move /leqifP.
case wx: (sorted ggen l); first by rewrite - (ZeckP wx) hb !eqxx.
by case wy: (l == L) => //; rewrite (eqP wy).
Qed.


(** Least element of the canonical representation *)

Definition Zeck_li n := last n (Zeck n).

Lemma Zeck_val_bounded n: all (fun i => fib i.+2 <= n) (Zeck n).
Proof.
rewrite - {1} (Zeck_zeck_val n) /Zeck_val;  elim: (Zeck n) => // a l H.
rewrite /= big_cons leq_addr /=;apply /allP => [x /(allP H) h].
by apply: (leq_trans h); rewrite leq_addl.
Qed.

Lemma Zeck_val_bounded1 n: all (fun i => i < n) (Zeck n).
Proof.
apply/allP => x /(allP (Zeck_val_bounded n)) h.
exact: (leq_trans (fib_gen x.+1) h).
Qed.

Lemma Zeck_li_pr n: n != 0 ->  Zeck_li n < n.
Proof.
move: (Zeck_val_bounded1 n); rewrite/Zeck_li;case: n => // n. 
by rewrite (Zeck_S' n) => sa sb; apply: (allP sa); simpl; apply:mem_last.
Qed.

Lemma Zeck_li_prop1 n : all (leq (Zeck_li n)) (Zeck n).
Proof.
rewrite /Zeck_li; case: n => // n. 
move: (Zeck_prop1 (n:=n.+1) isT) => [a [l [pa -> _]]].
rewrite rev_cons last_rcons all_rcons (leqnn) /= all_rev.
by apply /allP => [x  /(allP (path_all_llen pa)) /ltnW /ltnW /=].
Qed.

Lemma Zeck_li_prop2 n k: 
   k < (Zeck_li n) -> all [pred z | k < z] (Zeck n).
Proof.
by move => h; apply/allP => [x /(allP (Zeck_li_prop1 n))]; apply: leq_trans.
Qed.

(** The function e *)

Definition Zeckp n := Zeck_valp (Zeck n).

Lemma Zeckp_0: Zeckp 0 = 0.
Proof. by rewrite /Zeckp Zeck_0 /Zeck_valp big_nil. Qed.

Lemma Zeckp_1: Zeckp 1 = 1.
Proof. by rewrite /Zeckp Zeck_1 /Zeck_valp big_cons big_nil. Qed.

Lemma Zeckp_eq0 n: (Zeckp n == 0) = (n == 0).
Proof. 
case:n; first by rewrite Zeckp_0.
by move => n; rewrite /Zeckp Zeck_S' /Zeck_valp big_cons addn_eq0 fib_eq0 //. 
Qed.

Lemma Zeckp_prop00 l: sorted gtn l -> 
  Zeckp (Zeck_val l) =  Zeck_valp l /\  
  odd_last(Zeck (Zeck_val l)) =  odd_last l. 
Proof.
move => h;rewrite /Zeckp; apply: Zeck_valp_same => //. 
  apply: sorted_ggenW; apply:Zeck_ggen.
exact:Zeck_zeck_val.
Qed.

Lemma Zeckp_prop0 l: sorted gtn l -> Zeckp (Zeck_val l) =  Zeck_valp l.
Proof. by move /Zeckp_prop00 => []. Qed.

Lemma Zeck_odd_last_prop l: sorted gtn l -> 
  odd_last(Zeck (Zeck_val l)) =  odd_last l. 
Proof. by move /Zeckp_prop00 => []. Qed.

Lemma Zeckp_prop1 (l: seq nat): uniq l -> Zeckp (Zeck_val l) =  Zeck_valp l.
Proof.
move /sorted_gtn;set l' := (rev (sort leq l)).
have hb:perm_eq (sort leq l) l by apply/perm_eqlP; apply: perm_sort.
have ha: forall (l: seq nat), perm_eq (rev l) l.
  by elim => // a s h; rewrite rev_cons perm_rcons perm_cons.
have hc: perm_eq l l' by rewrite perm_eq_sym;apply: (perm_eq_trans (ha _ ) hb).
have ->: (Zeck_val l) = (Zeck_val l') by apply: eq_big_perm.
have ->: (Zeck_valp l) = (Zeck_valp l') by apply: eq_big_perm.
apply: Zeckp_prop0.
Qed.

Lemma Zeckp_prop1_bis l:  all (leq 1) l -> uniq l ->
  Zeckp (Zeck_valp l) =  Zeck_valpp l.
Proof.
move => sb; rewrite (seq_prednK sb) /Zeck_valp /Zeck_valpp /succ_seq.
move/ map_uniq; rewrite big_map big_map; apply:Zeckp_prop1.  
Qed.

Lemma Zeckp_prop2 n : n = Zeckp n + Zeck_valpp (Zeck n).
Proof. by rewrite - {1} (Zeck_zeck_val n) /Zeckp Zeck_valppE. Qed.

Lemma Zeckp_prop2_bis l (s := [seq i.+1 | i <- l]):
  [/\ Zeck_valp s = Zeck_val l,  Zeck_valpp s = Zeck_valp l &
     Zeck_val l + Zeck_valp l = Zeck_val s].
Proof.
by rewrite (Zeck_valppE s) /s /Zeck_valp /Zeck_val /Zeck_valpp !big_map.
Qed.

Lemma Zeckp_le n: Zeckp n <= n ?= iff (n <= 1).
Proof. 
apply/leqifP; case:n => [ | [ | n]]; rewrite ? Zeckp_0 ? Zeckp_1 //=.
rewrite {2} (Zeckp_prop2 n.+2); apply: ltn_paddr.
rewrite Zeck_S' /Zeck_valpp big_cons; move: (fib_contentP n.+1) => /=.
case: (fib_content n.+1); [ rewrite !ltnS // | move => k _].
by rewrite addn_gt0 fib_gt0.
Qed.

Lemma Zeck_split a l x: sorted llen (a :: l) -> x <= fib a.+2 ->
    Zeckp (x + (Zeck_val l)) = Zeckp x + Zeckp (Zeck_val l).
Proof.
move => sr le1; move:(uniq_llen sr) (path_all_llen sr) => h sa.
rewrite (Zeckp_prop1 h) {2}/Zeckp - {1}(Zeck_zeck_val x) /Zeck_val /Zeck_valp.
rewrite - !big_cat /=; apply: Zeckp_prop1; rewrite cat_uniq h Zeck_uniq /=.
rewrite andbT; apply/negP => /hasP [t /(allP sa)] => /= /ltnW sb tz.
move:(leq_trans (allP (Zeck_val_bounded x) _ tz) le1). 
by rewrite leqNgt (fib_smonotone_bis sb).
Qed.

Lemma fib_sum_alt n: Zeck_val (iota 0 n) = (fib (n.+3)).-2.
Proof.  
rewrite - fib_sum /Zeck_val.  
have <-:(\sum_(0 <= i0 < n.+2) fib i0) = (\sum_(i0 < n.+2) fib i0).
     by rewrite big_mkord. 
rewrite big_nat_recl // add0n  big_nat_recl // add1n /= big_mkord.
elim: n; first by rewrite big_nil big_ord0.
by move => k H; rewrite iota_Sr sum_rcons addnC H big_ord_recr. 
Qed.

Lemma fib_sum_even_alt n: Zeck_valpp (mkseq double n) = (fib (n.*2.-1)).-1.
Proof. 
rewrite -fib_sum_even /Zeck_valpp; elim: n; first by rewrite big_nil big_ord0.
by move => n H; rewrite /= mkseq_succ sum_rcons addnC H big_ord_recr.
Qed.

Lemma fib_sum_odd_alt n: Zeck_valp (mkseq double n) = fib (n.*2).
Proof. 
rewrite -fib_sum_odd /Zeck_valp; elim: n; first by rewrite big_nil big_ord0.
by move => n H; rewrite /= mkseq_succ sum_rcons addnC H big_ord_recr.
Qed.

Lemma fib_sum_even_alt2 n: Zeck_val (mkseq double n) = (fib (n.*2.+1)).-1.
Proof.
move: (fib_sum_even_alt n.+1); rewrite doubleS succnK => <-.
rewrite /Zeck_val /Zeck_valpp; elim:n; first by rewrite big_cons !big_nil. 
by move => n H; rewrite /= mkseq_succ  mkseq_succ !sum_rcons doubleS H. 
Qed.

Lemma Zeckp_fib n: Zeckp (fib n.+2) = fib n.+1.
Proof. by rewrite /Zeckp Zeck_fib /Zeck_valp big_cons big_nil addn0. Qed.

Lemma Zeck_fib1 n: Zeck (fib n.*2.+1).-1 = rev (mkseq double n).
Proof.
rewrite - fib_sum_even_alt2 - Zeckv_rev; apply: (ZeckP (sorted_ggen_sdouble n)).
Qed.

Lemma Zeck_fib2 n: Zeck (fib n.*2.+2).-1 = rev (succ_seq (mkseq double n)).
Proof.
rewrite - doubleS -fib_sum_odd_alt /Zeck_valp /mkseq /= big_cons add1n succnK.
transitivity (Zeck (Zeck_val(rev (succ_seq [seq i.*2 | i <- iota 0 n])))).
  by rewrite iota_S /Zeck_val /succ_seq sum_rev !big_map.
by apply:ZeckP; rewrite rev_sorted sorted_llen_succ sorted_llen_mkseq_e.
Qed.

Lemma Zeckp_fiba n: Zeckp (fib (n.*2.+1)).-1 = fib n.*2.
Proof.
rewrite -fib_sum_odd_alt -fib_sum_even_alt2.
apply:(Zeckp_prop1);apply: (mkseq_uniq _ _ double_inj).
Qed.

Lemma Zeckp_fibb n: Zeckp (fib n.*2.+1).-2 = (fib n.*2).-1.
Proof.
rewrite -fib_sum_odd_alt - (fib_sum_even_alt2 n)  /Zeck_val /Zeck_valp /mkseq.
case: n; first by rewrite !big_nil Zeckp_0.
move => n; rewrite !map_cons !big_cons !add1n !succnK -/iota.
apply: Zeckp_prop1; apply: (mkseq_uniq _ _ double_inj). 
Qed.

Lemma Zeckp_fibc n: Zeckp (fib n.*2).-1 = (fib n.*2.-1).-1.
Proof.
case: n => [| n];  rewrite ? Zeckp_0 // -fib_sum_odd_alt -fib_sum_even_alt2.
set L := [seq z.*2.+1 | z <- iota 0 n].
rewrite /Zeck_valp/mkseq map_cons -/iota iota_S big_cons add1n succnK !big_map.
transitivity (Zeckp (Zeck_val L)); first by rewrite /L /Zeck_val big_map.
transitivity (Zeck_valp L); last by rewrite /Zeck_val /Zeck_valp !big_map.
apply:Zeckp_prop1; apply: (mkseq_uniq _ _ doubleS_inj).
Qed.

Lemma Zeckp_fibd n: Zeckp ((fib n.*2).-2) = (fib n.*2.-1).-1.
Proof.
case: n => [| [|n]]; rewrite ?Zeckp_0 //.
set L := [seq i.*2.+1 | i <- iota 1 n].
rewrite - fib_sum_odd_alt - fib_sum_even_alt /mkseq /=/ Zeck_valp /Zeck_valpp. 
rewrite! big_cons add0n addnCA add2n !succnK iota_S - map_comp. 
rewrite (map_comp succn (fun i => i.*2.+1)) -/L  big_map big_map.
have sa: sorted llen (1 :: L). 
  rewrite - [(1::L) ] / [seq i.*2.+1 | i <- iota 0 n.+1].
  by apply:sorted_llen_mkseq => u /=; rewrite doubleS !ltnS. 
by rewrite (Zeck_split sa) // Zeckp_1 (Zeckp_prop1 (uniq_llen sa)).
Qed.

Lemma Zeckp_prop3a n (e := Zeckp): e (n + e n) = n.
Proof.
rewrite -{1 3}(Zeck_zeck_val n) /e {2}/Zeckp; move:(Zeckp_prop2_bis (Zeck n)).
move => [Ha Hb Hc]; rewrite Hc - Ha.
by apply:Zeckp_prop1; rewrite (map_inj_uniq succn_inj) Zeck_uniq.
Qed.

Lemma Zeckp_prop3b n (e := Zeckp): Zeck_li n != 0 -> e (e n) = n - e n.
Proof.
rewrite /e - lt0n => /Zeck_li_prop2 => h.
rewrite {2} (Zeckp_prop2 n) addKn; apply:(Zeckp_prop1_bis h (Zeck_uniq n)).
Qed.

Lemma Zeckp_prop4a n (e := Zeckp): e (n + e n.-1) = n.
Proof.
rewrite /e; case: n => [|n]; first by rewrite !Zeckp_0.
move: (Zeck_prop1 (n:=n.+1) isT) => [a [l [ss _ ->]]].
have fp: 0 < fib (a.+2) by rewrite fib_gt0.
rewrite Zeckv_cons /Zeck_val; set q :=  \sum_(j <- l) fib j.+2.
rewrite -{2}(prednK fp) addSn succnK (Zeck_split ss (leq_pred (fib a.+2))).
set E1 := (fib a.+2 + Zeckp (fib a.+2).-1); set E2 := q + Zeckp q.
have eq2: q = Zeckp E2 by rewrite (Zeckp_prop3a q).
have eq3: E1 = if (odd a) then fib a.+3 else (fib a.+3).-1.
  rewrite /E1 -{1 2 4 5}(odd_double_half a); case: (odd a).
    rewrite add1n -doubleS Zeckp_fiba  -fibSS //.
  rewrite - doubleS Zeckp_fibc doubleS succnK.
  by rewrite (fibSS (a./2).*2.+1) {2} (fib_pos (a./2).*2) addnS.
have eq4: fib a.+2 = Zeckp E1.
  rewrite eq3; case h: (odd a); first by rewrite (oddE h) Zeckp_fib.
  by rewrite (evenE h) - doubleS  Zeckp_fiba.
move:(Zeckp_prop2_bis l) => [ha hb]. 
have <-: Zeckp q = Zeck_valp l by apply: Zeckp_prop1;apply: (uniq_llen ss).
rewrite addnACA /E2 /q; move => ->; rewrite -/(Zeck_val l) - ha; symmetry.
rewrite (Zeck_split  (a := a.+1)) => //.
+ by rewrite - eq4 // Zeckp_prop1 // (map_inj_uniq succn_inj) (uniq_llen ss).
+ by move: ss; rewrite - map_cons -sorted_llen_succ. 
+ by rewrite -/E1 eq3; case: (odd a) => //; apply: leq_pred.
Qed.

Lemma Zeckp_prop4b n (e := Zeckp): odd (Zeck_li n) ->
   (e (e n).-1).+1 = n - e n.
Proof.
have ->: n - e n = Zeck_valpp (Zeck n) by rewrite {1} (Zeckp_prop2 n) addKn.
case: n => // n; move: (Zeck_prop1 (n:=n.+1) isT) => [a [l [ss ww ee]]].
rewrite /e /Zeck_li {2} /Zeckp /Zeck_valp /Zeck_valpp ww rev_cons last_rcons.
move/oddE => ->; rewrite !sum_rcons ! sum_rev - doubleS.
rewrite -fib_sum_odd_alt /Zeck_valp - big_cat /= big_cons add1n succnK.
set u :=  ([seq i.*2 | i <- iota 1 a./2] ++ l).
move: (order_path_min transitive_llen ss) => sa.
have pb: all (leq 1) u. 
   rewrite all_cat; apply /andP; split. 
   + clear; by elim: (a./2) {2} (0) => // n H k /=.
   + by apply/allP => [x /(allP sa)]; case x.
have pa: uniq u.  
  rewrite cat_uniq;apply /and3P; split.
  + by rewrite (map_inj_uniq double_inj) iota_uniq.
  + apply/negP => /hasP [x /(allP sa) sb] /mapP [y].
    rewrite mem_iota ltnS - (leq_double y) => /andP [_ sc] se.
    rewrite se in sb;  move: (ltnW (leq_trans sb sc)).
    by rewrite ltnNge double_half_le.
  + apply: (uniq_llen ss).
move:(fib_sum_even_alt (a./2).+1). 
rewrite  (Zeckp_prop1_bis pb pa) /Zeck_valpp doubleS /mkseq /= big_cons add0n. 
by rewrite big_cat /= - addSn  => ->; rewrite fib_pos.
Qed.

(** * Maximal  representation *)

Definition gespec := [rel i j | (i == j.+1) || (i== j.+2) ].
Definition lespec := [rel i j | gespec j i].
Definition spec_sorted (l: seq nat) :=
    sorted gespec l && gespec (last 0 l).+1 0.

Lemma spec_sorted_nil: spec_sorted [::].
Proof. by []. Qed.

Lemma spec_sorted_rev l: 
  (spec_sorted (rev l)) = sorted lespec l && lespec 0 (head 0 l).+1.
Proof. by rewrite /spec_sorted rev_sorted - (head_rev 0 (rev l)) revK. Qed.
 
Lemma spec_sorted_rcons l i: 
  (spec_sorted (rcons l i)) = (sorted lespec (i:: rev l)) && (i <= 1).
Proof.
by rewrite - {1} (revK ((rcons l i))) spec_sorted_rev rev_rcons /= !eqSS leqn1.
Qed.

Lemma spec_sorted_sorted l: spec_sorted l -> sorted gtn l.
Proof.
move /andP => [h _]; move:h.
case: l => //= n s; elim: s n => //= m s IHs n /andP [ h /IHs ->].
rewrite andbT;case/orP: h => /eqP -> //.
Qed.

Lemma spec_sorted_rec a l: spec_sorted (a::l) = 
  (if l== nil then a <=1  else gespec a (head 0 l)) && spec_sorted l.
Proof.
case: l; first by rewrite -/(rcons nil a) spec_sorted_rcons andbT //.
by move => b l; rewrite /spec_sorted /= andbA.
Qed.

Definition max_rep n l:= spec_sorted l && (Zeck_val l == n).

Lemma max_rep_fib1 n: max_rep (fib n.*2.+1).-1  (rev (mkseq double n)).
Proof.
rewrite /max_rep - {2}(Zeck_fib1 n) Zeck_zeck_val eqxx andbT.
rewrite spec_sorted_rev; case: n => //n /=; rewrite andbT.
by elim: n (0) => // n H i /=; rewrite eqxx orbT H.
Qed.

Lemma max_rep_fib2 n: 
  max_rep (fib n.*2.+2).-1 (rev (succ_seq (mkseq double n))).
Proof.
rewrite /max_rep - {2}(Zeck_fib2 n) Zeck_zeck_val eqxx andbT.
rewrite spec_sorted_rev; case: n => //n /=; rewrite andbT.
by elim: n (0) => // n H i /=; rewrite eqxx orbT H.
Qed.

Lemma max_rep_fib3 n: 
  max_rep (fib n.*2.+2) (rev (0::(succ_seq (mkseq double n)))).
Proof.
rewrite /max_rep.
move:(max_rep_fib2 n) => /andP [sa sb].
rewrite Zeckv_rev Zeckv_cons - Zeckv_rev (eqP sb) add1n - fib_pos eqxx.
by move: sa; rewrite spec_sorted_rev spec_sorted_rev andbT //;case n. 
Qed.

Lemma max_rep_fib4 n: 
  max_rep (fib n.*2.+3) (rev (1:: (map double (iota 1 n)))).
Proof.
rewrite /max_rep.
move:(max_rep_fib1 n.+1) => /andP; rewrite /mkseq /=.
set s := [seq i.*2 | i <- iota 1 n]; move => [sa /eqP].
rewrite !Zeckv_rev !Zeckv_cons doubleS add1n add2n => ->.
by move: sa; rewrite !spec_sorted_rev  /s- fib_pos eqxx /= !andbT; case n.
Qed.


Lemma fib_partial_sum k n (L := k:: mkseq (fun i => (k.+1+ i.*2)) n) :
   \sum_(i <- L) (fib i) = fib (k + n.*2) /\ sorted gespec (rev L).
Proof.
have A i j:  j + (i.+1).*2 = j.+2 + i.*2.
   by rewrite doubleS - add2n addnA - (addn2 j). 
rewrite /L big_cons; clear L;split.
  elim:n k; first by move => k; rewrite /mkseq /= big_nil !addn0.
  move => n H k; rewrite /mkseq /= iota_S big_cons addn0 addnA.
  rewrite (addnC (fib k)) -fibSS A - H ! big_map.
  by congr addn; apply: eq_bigr => i _; rewrite A.
rewrite rev_sorted /=. 
case: n => // n; elim: n k => [k| n H k]; first by rewrite /= addn0 eqxx.
move:(H k.+2) => /= /andP [_].
rewrite A !addn0  !eqxx orbT /= (iota_S 1); congr (path _ k.+3).
by rewrite - map_comp; apply/eq_in_map  => i _; rewrite /= A.
Qed.

Lemma fib_partial_sum' k n (L := k:: mkseq (fun i => (k.+1+ i.*2)) n) :
  Zeck_val L = fib (k.+2 + n.*2) /\ sorted gespec (rev L).
Proof.
split; last by exact (proj2 (fib_partial_sum k n)).
rewrite -(proj1 (fib_partial_sum k.+2 n)).
rewrite /Zeck_val /L !big_cons ! big_map //.
Qed.

 
Lemma max_rep_prop1 (l: seq nat): sorted gtn l ->
 { l' | [/\ spec_sorted l', Zeck_val l = Zeck_val l' &
    size l <= size l' ?= iff (spec_sorted l)] }.
Proof.
move => h.
suff: {s: seq nat |
  [/\ spec_sorted s, Zeck_val l = Zeck_val s,
    size l <= size s ?= iff (spec_sorted l) & head 0 s <= head 0 l] }.
  move => [s [pa pb pc _ ]]; by exists s.
elim: l h; first by move => _; exists [::]. 
move => a l Hrec /= h; move: (Hrec (path_sorted h)).
move => [s [ha hb hc hd]].
case sa: (spec_sorted (a :: l)).
  by exists (a::l); split => //; apply /leqifP.
case lz: (l== nil).
  rewrite (eqP lz) Zeckv_cons Zeckv_nil.
  move: sa; rewrite addn0 {1}/spec_sorted /= !eqSS - leqn1 => /negbT.
  rewrite (eqP lz) - ltnNge => /subnK; rewrite subn2 addn2 /= =>av.
  set u := ((a.-2)./2).
  have ww: ((a.-2 == u.*2.+1) || (a.-2 == u.*2)).
    by rewrite -(odd_double_half a.-2) /u;case: (odd _); rewrite eqxx // orbT.
  case av2: (a.-2 == u.*2.+1).
  + rewrite - av (eqP av2) - doubleS.
    move: (max_rep_fib4 u.+1); set s1 := rev _; move=> /andP [he hf].
    have hg: 1 <= size s1 ?= iff false by apply /leqifP; rewrite /s1 size_rev.
    have hi: head 0 s1 <= (u.+1).*2.+1.
      rewrite /s1 /= head_rev /= last_map; case u => // v.
      rewrite last_iota add2n //.
    by rewrite - (eqP hf); exists s1.
  + move: ww; rewrite av2 /= => /eqP ww.
    rewrite - av ww - doubleS.
    move: (max_rep_fib3 u.+1); set s1 := rev _; move=> /andP [he hf].
    have hg: 1 <= size s1 ?= iff false by apply /leqifP; rewrite /s1 size_rev.
    have hi: head 0 s1 <= (u.+1).*2.
      rewrite /s1 /= head_rev /= !last_map; case u => // v.
      by rewrite last_iota add1n ltn_double.
    by rewrite - (eqP hf); exists s1.
set b := head 0 l.
set c := head 0 s.
have pa: l = b:: behead l by move: lz; rewrite /b; case l.
have pb: s = c:: behead s by move:hc => []; rewrite pa /c; case s.
rewrite -/c -/b in hd.
have lba: b < a by move: h; rewrite pa /= => /andP [].
case wa: (gespec a c).
  have ra: spec_sorted (a :: s). 
      by move:ha wa; rewrite pb /spec_sorted /= ; move => /andP[ -> ->] ->.
  have rb: ((a == b.+1) || (a == b.+2)).
    rewrite (eqn_leq _ b.+1) (eqn_leq _ b.+2) lba.
    by case/orP: wa => /eqP ->; rewrite! ltnS hd //= andbT (ltnNge c) orNb.
  exists(a:: s); rewrite !Zeckv_cons hb /= leqnn; split => //.
   move: hc; move: sa; rewrite /spec_sorted pa /= rb /= => ->.
  by move /leqifP => H; apply/leqifP; rewrite ltnS.
have lac: c.+2 < a.
  move: (leq_ltn_trans hd lba); rewrite leq_eqVlt; case /orP.
    by rewrite eq_sym => h1; move: wa; rewrite /= h1.
  rewrite leq_eqVlt; case /orP => //.
  by rewrite eq_sym => h1; move: wa; rewrite /= h1 orbT.
set n := (a -c.+1)./2; set k := a - n.*2.
have [kp1 /eqP kp2]: ((k == c.+1) ||(k == c.+2)) /\ (k + n.*2 == a). 
  move: (subnK lac); set v := a -c.+3; rewrite - {1} add2n addnA addn2 => v1.
  rewrite /k /n -v1 addnK -{1 3 5 8} (odd_double_half v.+2).
  case: (odd _); first by rewrite add1n addSnnS addKn addnC !eqxx orbT.
  by rewrite addKn addnC !eqxx.
case: (posnP n) => np.
  move:kp1 lac; rewrite /k np subn0; case ww: (a==c.+2).   
    by rewrite (eqP ww) ltnn.
  by rewrite orbF => /eqP -> /ltnW; rewrite ltnn.
move: (fib_partial_sum' k n) => []; cbv zeta; set l1 := _ :: _.
rewrite addSn addSn kp2 Zeckv_cons => <- => he.
exists  (rev l1 ++ s).
split => //.
+ move: he ha; rewrite /l1; set l2 := mkseq _ _; move: (split_rev k l2) => eq1.
  rewrite /spec_sorted {1 2} eq1 /= cat_path => -> /=.
  rewrite last_cat rev_cons last_rcons pb /= => /andP[-> ->]. 
  set x := last _ _.
  have: x = last k (rev (k :: l2)) by rewrite eq1 /x rev_cons. 
  by rewrite rev_cons last_rcons ! andbT => ->.
+ by rewrite  hb /Zeck_val big_cat sum_rev.
+ apply /leqifP; rewrite size_cat size_rev /l1/size_cat /= size_mkseq.
  by rewrite -(prednK np) addSn addSn ltnS ltnS (leq_trans hc) // leq_addl.
+ rewrite /l1 /= rev_cons cat_rcons -(prednK np)- (revK (k::s)) - rev_cat. 
  rewrite head_rev last_cat last_mkseq add0n - kp2 -{2} (prednK np) doubleS.
  by rewrite addnS addnS addSn ltnS. 
Qed.


Lemma max_rep_bound a l: spec_sorted (a::l) -> 
   (fib a.+3).-1 <= Zeck_val (a::l) < (fib a.+4).-1.
Proof.
move => h.
apply /andP; split; last first.
  by rewrite -ltnS - fib_pos  (Zeckv_bound0 (spec_sorted_sorted h)).
elim: l a h.
  move => a; rewrite Zeckv_cons Zeckv_nil spec_sorted_rec /= andbT. 
  by case: a => //; case.
move => a l Hrec b.
have H:= (fib_pos b).
rewrite spec_sorted_rec /= => /andP[ha /Hrec hb].
rewrite Zeckv_cons fibSS H addnS /= leq_add2l (leq_trans _ hb) //.
by case /orP: ha => /eqP <-; rewrite ? leqnn // fibSS {2} H addSn leq_addr.
Qed.


Lemma max_rep_unique (s s': seq nat) : spec_sorted s -> spec_sorted s' -> 
   Zeck_val s = Zeck_val s' ->  s = s'.
Proof.
have A a l: Zeck_val [::] = Zeck_val (a :: l) -> False.
  by rewrite Zeckv_nil => h; move: (Zeckv_pos a l); rewrite - h.
have B a l: spec_sorted (a::l) ->   
  (fib a.+3) <= (Zeck_val (a::l)).+1 < (fib a.+4).
  by rewrite fib_pos(fib_pos a.+3) !ltnS => /max_rep_bound.
elim: s' s; first by  case => // a l _ _; move/ esym /A.
move => a l Hrec  [_ _ /A //| a' l' sa sb sc].
move: (B _ _ sa); rewrite sc => sa'.
move /eqP: (fib_partition sa' (B _ _ sb)); rewrite !eqSS => /eqP aux.
move: sa sb sc; rewrite aux ! spec_sorted_rec => /andP[ _ hc] /andP[ _ hd].
by move /eqP; rewrite !Zeckv_cons eqn_add2l => /eqP h; rewrite (Hrec l'). 
Qed.

Definition ZeckM n := sval (max_rep_prop1  (sorted_ggenW (Zeck_ggen n))).

Lemma ZeckM_prop1 n: 
  [/\ spec_sorted (ZeckM n), Zeck_val (Zeck n) = Zeck_val (ZeckM n)
    & size (Zeck n) <= size (ZeckM n) ?= iff spec_sorted (Zeck n)].
Proof.
exact :(svalP (max_rep_prop1  (sorted_ggenW (Zeck_ggen n)))).
Qed.

Lemma ZeckM_prop2 n: max_rep n (ZeckM n).
Proof. 
rewrite /max_rep;  move: (ZeckM_prop1 n) => [-> <- _]. 
by rewrite (Zeck_zeck_val n)  eqxx.
Qed.

Lemma ZeckM_prop3 n l: max_rep n l -> ZeckM n = l.
Proof.
move:(ZeckM_prop2 n) => /andP[ha /eqP hb] /andP[hc /eqP hd].
by apply:max_rep_unique => //; rewrite hb.
Qed.

Lemma ZeckM_is_maximal n l: sorted gtn l -> Zeck_val l = n ->
    size l <= size (ZeckM n) ?= iff (l == (ZeckM n)).
Proof.
move: (ZeckM_prop1 n) => [ha hb whc].
rewrite  (Zeck_zeck_val n) in hb.
move => /max_rep_prop1 [s [hc hd  /leqifP M]] he.
case wx: (spec_sorted l).
  by rewrite hb in he; rewrite (max_rep_unique wx ha he);  apply/leqif_refl.
apply/leqifP; move: M; rewrite he hb in hd;rewrite wx (max_rep_unique ha hc hd).
by case H: (l==s) => //; rewrite (eqP H).
Qed.

Lemma ZeckM_prop4 n l: sorted gtn l -> Zeck_val l = n ->
  (size (Zeck n) <= size l <= size (ZeckM n) /\
  (size (Zeck n) = size (ZeckM n) -> l = (Zeck n))).
Proof.
move => pa pb.
move: (ZeckM_is_maximal pa pb) => [pc pd].
move: (Zeck_is_minimal pa pb) => [pe pf].
by rewrite pc pe; split => // h;apply /eqP; rewrite - pf eqn_leq pe h pc.
Qed.

Lemma unique_representation n:
  (exists k, n = (fib k.+2).-1) <-> 
   (forall l l', sorted gtn l -> Zeck_val l = n ->
     sorted gtn l' -> Zeck_val l' = n -> l = l').
Proof.
split.   
  move => [k nv].
  have pa: Zeck n  = ZeckM n.
   case: (odd_dichot k) => kv.
     have ->: n = (fib((k./2.+1).*2.+1)).-1 by rewrite nv {1} kv /= doubleS.
     by rewrite (ZeckM_prop3  (max_rep_fib1 (k./2.+1))) -(Zeck_fib1 (k./2.+1)).
   by rewrite nv kv (ZeckM_prop3  (max_rep_fib2 k./2)) (Zeck_fib2 k./2).
  have pb: (size (Zeck n) = size (ZeckM n)) by rewrite pa.
  move => l l' la ea lb eb.
  by rewrite (proj2 (ZeckM_prop4 la ea) pb) (proj2 (ZeckM_prop4 lb eb) pb).
move => H.
move: (ZeckM_prop2 n) => /andP [/spec_sorted_sorted  ha /eqP hb].
move: (sorted_ggenW (Zeck_ggen n)) => hc.
move: (Zeck_zeck_val n) => hd; rewrite - hd.
move: (ZeckM_prop1 n)=> []; rewrite (H _ _ ha hb hc hd) => [he _ _].
case: (posnP n) => np.
    by exists 0; rewrite np  Zeckv_nil.
rewrite lt0n in np;move: (Zeck_prop1 np) => [a [l [pa pb pc]]].
suff: a::l = (mkseq double (size l).+1) 
   \/ a ::l =  (succ_seq (mkseq double (size l).+1)).
  rewrite pb; case => ->.
     by exists ((size l).*2.+1); rewrite -Zeck_fib1 Zeck_zeck_val.
  by exists ((size l).*2.+2); rewrite -Zeck_fib2 Zeck_zeck_val.
move: he pa; rewrite pb spec_sorted_rev /= !eqSS.
move => /andP [pd pe] pf.
suff: a :: l = [seq i+a | i<- mkseq double (size l).+1].
  move => ->; rewrite /mkseq /succ_seq -!map_comp /comp.
  case: (orP pe) => av; rewrite (eqP av); [left | right].
    by apply/eq_in_map => i _; rewrite addn0.
  by simpl; congr cons; apply/eq_in_map => i _; rewrite addn1.
move: pd pf; clear; elim: l a => [a // | a l Hr b]. 
simpl => /andP[ ha hb] /andP[hc hd].
case: (orP ha) => ha'; first by move: hc; rewrite (eqP ha') ltnn.
rewrite Hr //= (eqP ha') (iota_S 1) /succ_seq -! map_comp /comp /=.
by congr cons; congr cons; apply/eq_in_map => i _;rewrite !addnS ! addSn //.
Qed.


Lemma iota_lespec_sorted i n: sorted lespec (iota i n).
Proof. 
by elim: n i => //; case => // n H i /=; rewrite eqxx /=; apply: H.
Qed.


Lemma iota_rem_lespec_sorted i j n: sorted lespec (rem j (iota i n)).
Proof.
elim: n i j; first by move => n k /=; case (n == k).
move => j H i k /=; case: (i==k); first by apply: iota_lespec_sorted.
move: (H i.+1 k);case j => // j1 /=; case:(i.+1 == k) => //;
  case: j1 => // j2 /=;  rewrite eqxx // orbT //.
Qed.

Lemma iota_rem_spec_sorted j i: spec_sorted (rev (rem i (iota 0 j))).
Proof.
rewrite spec_sorted_rev; apply/andP; split;last first.
  case:j => // j /=;case ww: (0 == i) => //; case:j => //.
by apply: iota_rem_lespec_sorted. 
Qed.


Lemma iota_rem2_spec_sorted j i: 
  spec_sorted (rev (rem i.+2 (rem i (iota 0 j)))).
Proof.
rewrite spec_sorted_rev; apply/andP; split;last first.
  case:j => // j /=;case ww: (0 == i) => //; case:j => //.
elim: j 0 i; first by move => n k /=; case (n == k).
move => j H i k /=; case: (i==k); first by apply:iota_rem_lespec_sorted.
simpl; case ww:(i == k.+2); first by apply:iota_rem_lespec_sorted.
move: (H i.+1 k); clear; case: j => // j /=.
case wwb: (i.+1 == k). 
  have wwc: k == k.+1 = false by apply/negP => /eqP; exact: n_Sn.
  by case:j => // j /=; rewrite eqSS (eqP wwb) wwc /= (eqP wwb) eqxx orbT.
rewrite /= eqSS; case wwc: (i == k.+1); last by rewrite /= eqxx.
rewrite (eqP wwc);case: j => // j /=.
by rewrite gtn_eqF /= ?eqxx ?orbT // ltnS - addn2 leq_addr.
Qed.

Lemma ZeckM_bound1 n (a := head 0 (ZeckM n)):
  0 < n -> (fib a.+3).-1 <= n < (fib a.+4).-1.
Proof.
rewrite /a; move/andP:(ZeckM_prop2 n) => [ h /eqP {1 3 4} <-]. 
by move: h;case: (ZeckM n) => [| b l / max_rep_bound //]; rewrite Zeckv_nil.
Qed.

Lemma ZeckM_bound2 n a: 
  (fib a.+3).-1 <= n < (fib a.+4).-1  -> a = head 0 (ZeckM n).
Proof.
case: (posnP n) => np; first by rewrite np fib_ge2_alt.
rewrite -ltnS -(ltnS n.+1) -!fib_pos => la.
move:(ZeckM_bound1 np); rewrite -ltnS -(ltnS n.+1)  -!fib_pos => lb.
by move /eqP:(fib_partition la lb); rewrite !eqSS => /eqP.
Qed.

Lemma ZeckM0: ZeckM 0 = [::].
Proof. by apply:ZeckM_prop3; rewrite /max_rep Zeckv_nil. Qed.

Lemma ZeckM1: ZeckM 1 = [:: 0].
Proof. by apply:ZeckM_prop3; rewrite /max_rep Zeckv_cons Zeckv_nil. Qed.

Lemma ZeckM2: ZeckM 2 = [:: 1].
Proof. by apply:ZeckM_prop3; rewrite /max_rep Zeckv_cons Zeckv_nil. Qed.

Lemma ZeckMgt2 n: 2 <n -> 2 <= size (ZeckM n).
Proof.
move/andP:(ZeckM_prop2 n)=> []; case: (ZeckM n).
  by rewrite Zeckv_nil => _ /eqP <-.
move => a l; rewrite spec_sorted_rec /= ltnS; case:l => //=.
by rewrite Zeckv_cons Zeckv_nil leqn1 => /andP []; case/orP=> /eqP -> _ /eqP <-.
Qed.

Lemma ZeckM_rec1 n a: (fib a.+3).-1 <= n < (fib a.+4).-1 ->
  ZeckM (n + (fib a.+3)) = a.+1::ZeckM n.
Proof.
move /ZeckM_bound2 => sa.
move/andP: (ZeckM_prop2 n) => [ss /eqP nv].
apply:ZeckM_prop3; rewrite/max_rep Zeckv_cons nv addnC eqxx.
by rewrite spec_sorted_rec ss sa; case:(ZeckM n) => // nb l /=; rewrite eqxx.
Qed.

Lemma ZeckM_rec2 n a: (fib a.+3).-1 <= n < (fib a.+4).-1 ->
  ZeckM (n + (fib a.+4)) = a.+2::ZeckM n.
Proof.
case: (posnP n) => np; first by rewrite np fib_ge2_alt.
move/ZeckM_bound2 => sa.
move/andP: (ZeckM_prop2 n) => [ss /eqP nv].
apply:ZeckM_prop3; rewrite/max_rep Zeckv_cons nv addnC eqxx spec_sorted_rec.  
move: np; rewrite - {1}nv sa ss; case:(ZeckM n); first by rewrite Zeckv_nil.
by move => // b l _ /=;rewrite eqxx orbT.
Qed.

Lemma ZeckM_fibm2 n:  ZeckM (fib (n.+3)).-2 = rev (iota 0 n).
Proof.
apply:ZeckM_prop3; apply/andP; split.
   rewrite spec_sorted_rev; case: n => // n /=; rewrite andbT.
   by elim:n (0) => // k H n /=; rewrite H eqxx.
rewrite  /Zeck_val - fib_sum !big_ord_recl /=.
elim:n => [|n Hr];first by rewrite big_nil big_ord0.
by rewrite big_ord_recr - (eqP Hr) iota_Sr rev_rcons big_cons addnC.
Qed.


Lemma size_sorted a l:
  sorted gtn (a::l) -> size l <= a ?= iff (l == rev (iota 0 a)).
Proof.
elim: l a => [a _|b l Hrec a].
  by apply /leqifP; case:a => // a; rewrite iota_Sr rev_rcons //.
move => /= /andP [lba /Hrec ha]. 
  split.  rewrite (leq_ltn_trans _ lba) //;apply: ha.
move: lba; case: a => // a. rewrite ltnS => lab.
rewrite iota_Sr rev_rcons add0n eqseq_cons eqSS.
have sl: size l <= b by apply: ha.
move/leqifP: ha; move: lab; rewrite leq_eqVlt; case /orP => hx.
  by rewrite -(eqP hx) eqxx; case: eqP => // _ /ltn_eqF ->.
rewrite (ltn_eqF hx) /= => _; exact: (ltn_eqF (leq_ltn_trans sl hx)).
Qed.


Lemma ZeckM_bound3 n a:
  (fib a.+3).-1 <= n < (fib a.+4).-1 ->
  size (ZeckM n) <= a.+1 ?= iff (n== (fib (a.+4)).-2).
Proof.
move => h.
move:(ZeckM_bound2 h); move: (ZeckM_prop2 n) h => /andP[];case: (ZeckM n).
   by rewrite Zeckv_nil => _ /eqP <-; rewrite fib_ge2_alt /=.
move => b l ss zv _ /= ->; apply/leqifP.
move:(ZeckM_prop2 (fib b.+4).-2) => /andP[wa /eqP zz].
case: eqP => nv.
  have ea: Zeck_val (b :: l) = Zeck_val (ZeckM (fib b.+4).-2).
    by rewrite zz -nv (eqP zv).
  rewrite -/(size (b::l)) (max_rep_unique ss wa ea) ZeckM_fibm2. 
  by rewrite size_rev size_iota.
move /leqifP: (size_sorted (spec_sorted_sorted ss)); rewrite ltnS. 
case: eqP => // lv; move: zv; rewrite lv  -rev_rcons -iota_Sr - ZeckM_fibm2 zz. 
by move => h;case: nv; rewrite (eqP h).
Qed.


Definition card_max_rep n m:=
   \sum_((fib n).-1 <= i < (fib n.+1).-1) (size (ZeckM i)== m).

Lemma  card_max_repE n m: 
  card_max_rep n m =
    \sum_((fib n).-1 <= i < (fib n.+1).-1 | (size (ZeckM i)== m)) 1.
Proof. by rewrite big_mkcond /= /card_max_rep; apply: eq_big. Qed.

Lemma card_max_rep0m m: card_max_rep 0 m = 0.
Proof. by rewrite/card_max_rep /= big_geq. Qed.

Lemma card_max_rep1m m: card_max_rep 1 m = 0.
Proof. by rewrite/card_max_rep /= big_geq. Qed.

Lemma card_max_rep2m m: card_max_rep 2 m = (m==0).
Proof. 
by rewrite/card_max_rep big_ltn // big_geq // fibE /= ZeckM0 addn0 eq_sym.
Qed.

Lemma card_max_rep41: card_max_rep 4 1 = 1.
Proof.
by rewrite /card_max_rep big_ltn// big_ltn// big_geq//= ZeckM2 (ZeckM_fibm2 2).
Qed.


Lemma card_max_rep_smalln n m: n < m.+2 -> card_max_rep n m = 0.
Proof.
case:n => [|[| [|n]]]; rewrite ? card_max_rep0m ? card_max_rep1m // ! ltnS. 
  by move/gtn_eqF; rewrite  card_max_rep2m => ->.
move => lnm; rewrite card_max_repE big_hasC => //; apply /hasPn => x.
rewrite mem_index_iota => ltn; apply/eqP => eq1.
by move:(leq_ltn_trans (ZeckM_bound3 ltn) lnm); rewrite eq1 ltnn.
Qed.

Lemma card_max_repn0 n: card_max_rep n.+3 0 = 0.
Proof.
rewrite card_max_repE big_hasC => //; apply /hasPn => i.
rewrite mem_index_iota size_eq0 => fb; apply /eqP => ln.
move: (ZeckM_prop2 i); rewrite /max_rep ln Zeckv_nil => /andP[_ /eqP iz].
by move: fb; rewrite - iz leqn0 (fib_ge2_alt).
Qed.

Lemma card_max_repn2n n: card_max_rep n.+2 n = 1.
Proof.
move: (fib_ge2_alt n); set p :=  (fib n.+3).-2 => pv.
have la: (fib n.+2).-1 <= p by rewrite - 2!ltnS -pv -fib_pos fib_smonotone_bis.
have lb: p <= (fib n.+3).-1 by rewrite pv /=.
rewrite card_max_repE (big_cat_nat _ _ _ la lb) pv /= big_hasC.
  by rewrite big_ltn_cond // /p ZeckM_fibm2 size_rev size_iota eqxx big_geq.
apply/hasPn => i; rewrite mem_index_iota /p.
case:(posnP n)=> [ | /prednK nv]; first by move ->; rewrite ltn0 andbF.
rewrite ltn_neqAle (andbC  (i != _)) andbA -(ltnS i) -/p -[p.+1]/(p.+2.-1) -pv. 
rewrite -nv => /andP [] /ZeckM_bound3 /leqifP; rewrite nv; case:eqP => //.
by move => _ /ltn_eqF ->.
Qed.


Lemma card_max_rep_rec n m: m.+2 <= n ->
  card_max_rep n.+2 m.+1 = card_max_rep n.+1 m + card_max_rep n m.
Proof.
case: m.
  case:n => [|[ | [| n _]]] //; rewrite !card_max_repn0.
    by rewrite card_max_rep41 card_max_rep2m.   
  rewrite card_max_repE big_hasC => //; apply /hasPn => i.
  rewrite mem_index_iota => /andP [la _].
  have l2n3: 2 < n.+3 by rewrite !ltnS.
  move: (fib_smonotone_bis l2n3); rewrite (fib_pos n.+4) ltnS => lb.
  by rewrite (gtn_eqF (ZeckMgt2 (leq_trans lb la))).
move => m lmn.
set k :=  (fib n.+1) +  (fib n.+1).-1. 
have kl1: (fib n.+2).-1 <= k.
   by rewrite - ltnS /k -addnS -!fib_pos fibSS leq_add2l fib_monotone.
have kl2: k <= (fib n.+3).-1.
  by rewrite - ltnS /k -addnS -!fib_pos fibSS leq_add2r fib_monotone.
have np:=(ltn_predK lmn).
have n3: n = (n-3).+3 by rewrite - addn3 subnK // (leq_trans _ lmn).
rewrite addnC !card_max_repE (big_cat_nat _ _ _ kl1 kl2) /=; congr addn. 
   rewrite fibSS /k -[in fib n] np (fib_pos n.-1) addnS /= np big_nat_shift.
   apply:big_nat_cond_eq => i eq1.
   by rewrite n3 in eq1; move:(ZeckM_rec2 eq1); rewrite -n3 addnC => ->.
rewrite fibSS /k (addnC (fib n.+2)) (fib_pos n.+1)  addnS /= big_nat_shift. 
apply:big_nat_cond_eq => i eq1.
by rewrite n3 in eq1; move:(ZeckM_rec1 eq1); rewrite -n3 addnC => ->.
Qed.

Lemma card_max_rep_val n m: m.+2 <= n -> card_max_rep n m = 'C(m,n- m.+2).
Proof.
move/subnK => {1} <-; set k := _ - _; move: k; elim: {n} m.
  case; first by rewrite card_max_rep2m.
  by move => k; rewrite bin0n /= addn2 card_max_repn0.
move => n Hr; case; first by rewrite card_max_repn2n bin0.
move => k; rewrite 2!addnS card_max_rep_rec ?ltn_paddl //. 
by rewrite addSnnS Hr - addSn Hr - binS.
Qed.


Definition card_min_rep n m:=
   \sum_((fib n) <= i < (fib n.+1)) (size (Zeck i)== m).

Lemma card_min_repE n m: 
  card_min_rep n m =
    \sum_((fib n) <= i < (fib n.+1)| (size (Zeck i)== m)) 1.
Proof. by rewrite big_mkcond /= /card_min_rep; apply: eq_big. Qed.

Lemma card_min_rep0m m: card_min_rep 0 m = (m==0).
Proof. by rewrite /card_min_rep big_nat1 Zeck_0 eq_sym. Qed.

Lemma card_min_rep1m m: card_min_rep 1 m = 0.
Proof. by rewrite /card_min_rep big_geq. Qed.

Lemma card_min_rep2m m: card_min_rep 2 m = (m==1).
Proof. by rewrite /card_min_rep big_nat1 Zeck_1 eq_sym. Qed.

Lemma card_min_repn0 n: card_min_rep n 0 = (n==0).
Proof.
case nz: (n==0); first by rewrite  (eqP nz) card_min_rep0m.
rewrite card_min_repE big_hasC => //; apply /hasPn => i.
rewrite mem_index_iota=> /andP[ha _]; rewrite size_eq0; move:(Zeck_zeck_val i).
move: ha; case:i; first by rewrite leqn0 fib_eq0 nz.
by move=> i; case: (Zeck i.+1) => //; rewrite Zeckv_nil.
Qed. 

Lemma card_min_repn1 n: card_min_rep n 1 = (2 <=n).
Proof.
case: n=> [|[|n]]; rewrite ? card_min_rep0m ?card_min_rep1m //=.
rewrite card_min_repE big_ltn_cond ?fib_smonotone_bis // Zeck_fib /=.
rewrite big_hasC => //; apply /hasPn => i.
rewrite mem_index_iota=> /andP[ha hb]; move:(Zeck_zeck_val i).
case:(Zeck i) => // a [|b l //]; rewrite Zeckv_cons Zeckv_nil addn0 => h.
move:hb; rewrite - h => /fib_monotone_bis; rewrite ltnS => /fib_monotone.
by rewrite h leqNgt ha.
Qed.


Lemma card_min_rep_rec n m:
  card_min_rep n.+2 m.+1 = card_min_rep n.+1 m.+1 + card_min_rep n m.
Proof.
case: (posnP n) => np.
  by rewrite np card_min_rep1m  card_min_rep0m card_min_rep2m eqSS.
set k := fib n.+2 + fib n.
have kl1: (fib n.+2) <= k by rewrite leq_addr.
have kl2: k <= (fib n.+3) by rewrite  fibSS /k leq_add2l fib_monotone.
rewrite {1} card_min_repE (big_cat_nat _ _ _ kl1 kl2) /=; congr addn. 
  rewrite /k {1} fibSS !(addnC _ (fib n)) big_nat_shift card_min_repE.
  apply:big_nat_cond_eq => i eq1.
  move/andP:(eq1) => [ha]; rewrite fibSS => hb.
  have ww:(fib n + i - fib n.+2) = (i - fib n.+1).
    by rewrite -{1} (subnKC ha) addnA (addnC (fib _)) - fibSS addKn.
  have eq2: fib n.+2 <= fib n + i < fib n.+3. 
     rewrite !fibSS addnC leq_add2l -addnA ltn_add2l ha /=. 
     by apply: (leq_trans hb); rewrite  leq_add2l fib_monotone.
  rewrite - (prednK np) in eq1.
  by rewrite (Zeck_S eq1) (prednK np)  (Zeck_S eq2) ww.
rewrite fibSS /k big_nat_shift card_min_repE.
apply:big_nat_cond_eq => i /andP [ha hb].
have eq2: fib n.+2 <= fib n.+2 + i < fib n.+3. 
  by rewrite leq_addr /= (fibSS n.+1) ltn_add2l. 
by rewrite (Zeck_S eq2) addKn /= eqSS.
Qed.


Lemma card_min_rep_small n m: 0 < n <= m -> card_min_rep n m = 0.
Proof.
case: n => [| [| n /= lnm]] //; first by rewrite card_min_rep1m.
rewrite card_min_repE big_hasC => //; apply /hasPn => i.
rewrite mem_index_iota => eqa.
move: (sorted_ggenW (Zeck_ggen i)); rewrite (Zeck_S eqa)  => /size_sorted /=.
set s := size _ => ls.
have lsn: s.+2 <= n.+2 by rewrite !ltnS; apply:ls.
by rewrite (ltn_eqF (leq_trans lsn lnm)).
Qed.


Lemma card_min_rep_val n m :  card_min_rep (n+m.+2) m.+1 = 'C(n,m). 
Proof.
elim:n m. 
  case; first by rewrite card_min_repn1.
  by move => m; rewrite bin0n card_min_rep_rec  !card_min_rep_small /=.
move => n H; case; first by rewrite bin0; rewrite card_min_repn1 addn2 //.
by move => m; rewrite 2!addnS  card_min_rep_rec addSnnS -addnS H H binS.
Qed.

Lemma card_min_rep_valbis n m: 0< m< n ->
   card_min_rep n m = 'C(n-m-1,m.-1). 
Proof.
move => /andP[sa sb]; rewrite -subnDA -{1}(subnK sb) addn1 -{2 3} (prednK sa). 
by rewrite card_min_rep_val.
Qed.

Section DualUniqueRepresentation.

Parameter v: nat -> nat.
Definition Zval_v l:= \sum_(i <- l) (v i).
Hypothesis v_exists:
  forall n, exists2 l, spec_sorted l & Zval_v l = n.
Hypothesis v_unique:
  forall l l', spec_sorted l ->  spec_sorted l' -> Zval_v l = Zval_v l' ->
   l = l'.



Lemma DUR_injv: injective v.
Proof.
move => i j sv.
set l:= iota 0 (i+j).+1.
have Ha: forall k, k\in l ->  Zval_v l = Zval_v (k :: rem k l). 
  by move => k H;  apply: eq_big_perm; apply:perm_to_rem.
have il: i \in l by  rewrite mem_iota /= ltnS leq_addr.
have : Zval_v (i :: rem i l) = Zval_v (j :: rem j l).
  by rewrite - Ha // -  Ha // mem_iota /= ltnS  leq_addl.
move/eqP; rewrite /Zval_v !big_cons sv eqn_add2l - sum_rev.
rewrite - [ X in _ == X] sum_rev  => /eqP eq1.
have Hb:= (iota_rem_spec_sorted (i+j).+1).
move: (v_unique (Hb i) (Hb j) eq1) => /rev_inj eq2.
case ok:(i== j); first by rewrite (eqP ok).
have ul: uniq l by apply: iota_uniq.
have: i \in rem j l by rewrite mem_rem_uniq // inE ok.
by rewrite - eq2 mem_rem_uniq // inE // eqxx.
Qed.


Lemma DUR_positive i: 0 < v i.
Proof.
case: (posnP (v i)) => // h.
have ha j: spec_sorted (rev(iota 0 j)).
  rewrite  spec_sorted_rev; apply/andP; split; last by case:j.
  by elim: j 0 => // j H k /=; move:(H k.+1); case j => // m /=; rewrite eqxx.
move:(v_unique (ha i)(ha i.+1)).
rewrite /Zval_v !sum_rev iota_Sr sum_rcons h add0n => H.
have: i \in (iota 0 i) by  rewrite (rev_inj (H (erefl _))) mem_rcons inE eqxx.
by rewrite mem_iota // ltnn andbF.
Qed.


Lemma DUR_exclusion1 i: v i + v i.+2 != v i.+1.
Proof.
case eqP => // eq1.
set l := iota 0 i.
set l1 := rev(rcons (rcons l i) i.+2).
set l2 := rev (rcons l i.+1).
have ea:Zval_v l1 = Zval_v l2. 
  by rewrite /Zval_v /l1 /l2 !sum_rev !sum_rcons addnA (addnC _ (v i)) eq1.
have eb: l1 = rev (rem i.+1 (iota 0 i.+3)).
  congr rev; rewrite iota_Sr iota_Sr add0n rem_rcons1 //.
  by rewrite - iota_Sr rem_rcons2 // mem_iota ltnn andbF.
have ec: l2 = rev (rem i (iota 0 i.+2)).
  congr rev; rewrite /l iota_Sr iota_Sr ! add0n; rewrite rem_rcons1 //.
  by rewrite rem_rcons2 // mem_iota ltnn andbF. 
have sa: spec_sorted l1 by rewrite eb; apply: iota_rem_spec_sorted.
have sb: spec_sorted l2 by rewrite ec; apply: iota_rem_spec_sorted.
move:(v_unique sa sb ea); rewrite eb ec => /rev_inj => ed.
move: (f_equal size ed); rewrite !size_rem ?size_iota ? mem_iota ?ltnS //=.
by move/esym /n_Sn.
Qed.

Lemma DUR_exclusion2 i: v i + v i.+2 != v i.+1 + v i.+3.
Proof.
case eqP => // eq1.
set l := iota 0 i.
set l1 := rev(rcons (rcons l i) i.+2).
set l2 := rev (rcons (rcons l i.+1) i.+3).
have ea:Zval_v l1 = Zval_v l2. 
  rewrite /Zval_v /l1 /l2 !sum_rev !sum_rcons !addnA (addnC _ (v i)) eq1.
  by rewrite (addnC _ (v i.+1)).
have eb: l1 = rev (rem i.+1 (iota 0 i.+3)).
  congr rev; rewrite iota_Sr iota_Sr add0n rem_rcons1 //.
  by rewrite - iota_Sr rem_rcons2 // mem_iota ltnn andbF.
have ec: l2 = rev (rem i.+2 (rem i (iota 0 i.+4))).
  have ha: i < i.+3 by  rewrite !ltnS; apply: (@leq_trans i.+1).
  have hb: i \notin iota 0 i by rewrite mem_iota ltnn andbF.
  congr rev; rewrite ! iota_Sr !add0n rem_rcons1 // rem_rcons1 //.
  rewrite rem_rcons1 // rem_rcons2 // rem_rcons1 //  rem_rcons2 //.
  by rewrite mem_rcons inE mem_iota /= negb_or  gtn_eqF //= - leqNgt.
have sa: spec_sorted l1 by rewrite eb; apply: iota_rem_spec_sorted.
have sb: spec_sorted l2 by rewrite ec; apply: iota_rem2_spec_sorted. 
move:(v_unique sa sb ea); rewrite eb ec => /rev_inj => ed.
have: i.+2 \in rem i.+1 (iota 0 i.+3).
  rewrite 2!iota_Sr !add0n rem_rcons1 // rem_rcons2 // ?mem_iota ?ltnn //.
   by rewrite mem_rcons inE eqxx.
rewrite ed mem_rem_uniq ?inE ?eqxx //; apply/ rem_uniq/iota_uniq.
Qed.



Lemma DUR_01 : v 0 = 1 /\ v 1 = 2.
Proof.
have Ha a b l: spec_sorted [:: a, b & l] -> 2 < Zval_v (a::b::l).
  move => /spec_sorted_sorted nab; rewrite /Zval_v !big_cons addnA. 
  apply:(@leq_trans ( v a + v b)); last by apply leq_addr.
  move:(DUR_positive a) (DUR_positive b) => ha hb.
  move: ha; rewrite leq_eqVlt => /orP; case => ha; last exact:(leq_add ha hb).
  move: hb;rewrite leq_eqVlt => /orP; case=> hb;last by rewrite -(eqP ha) ltnS.
  have eab: a = b by apply:DUR_injv; rewrite - (eqP ha) -(eqP hb).
  by move/andP: nab=> []; rewrite eab /gtn /= ltnn.
move: (v_exists 2)  => [[| b l]]; first by rewrite /Zval_v big_nil //.
case:l; last by move => a l /Ha ha hb; move: ha; rewrite hb. 
rewrite spec_sorted_rec /Zval_v big_cons big_nil addn0/= => /andP [pa _] pb.
move: (v_exists 1)  => [[| a l]]; first by rewrite /Zval_v big_nil //.
case:l; last by move => c l /Ha ha hb; move: ha; rewrite hb. 
rewrite spec_sorted_rec /Zval_v big_cons big_nil addn0/= => /andP [pc _] pd.
move: pc; rewrite leqn1; case/orP => /eqP pc.
  rewrite - pb - {1} pd; move: pa; rewrite leqn1; case/orP => /eqP pa.
    have //: 1 = 2 by rewrite - pb - pd pa pc.
  by rewrite pa pc.
move: pa; rewrite leqn1; case/orP => /eqP pa; last first.
  have //: 1 = 2 by rewrite - pb - pd pa pc.
move: pb pd; rewrite pa pc => v0 v1; clear a b pa pc.
have Hb: forall i, 2 <= i -> 3 <= v i.
  move => i i2;rewrite !ltn_neqAle; case: eqP.
   by rewrite - v0; move/DUR_injv => h; move: (ltnW i2); rewrite h ltnn.
  case: eqP; first by rewrite -v1;move/DUR_injv => h; move: i2; rewrite h ltnn.
  by rewrite eq_sym (lt0n_neq0 (DUR_positive i)).
have Hc a b c l: spec_sorted [:: a, b,c & l] -> 6 <= Zval_v (a::b::c::l).
  move => /spec_sorted_sorted nab; rewrite /Zval_v !big_cons !addnA. 
  apply:(@leq_trans (v a + v b + v c)); last by apply leq_addr.
  move: nab => /= /andP [lta /andP [ltb _]].
  move: (leq_ltn_trans (leq0n c) ltb); rewrite - ltnS => ltc. 
  move:(Hb _ (leq_trans ltc lta)) => ltd; case:(leqP b 1).
    rewrite leqn1; case/orP => /eqP bv; move:ltb; rewrite bv //.
    by rewrite ltnS leqn0 => /eqP ->; rewrite v0 v1 addn1 addn2 !ltnS.
  move/Hb => lte; move:(leq_add ltd lte) => ltf;apply(leq_trans ltf).
  by rewrite leq_addr.
have Hd: Zval_v [::] = 0 by rewrite / Zval_v big_nil.
have He a:spec_sorted [:: a] -> Zval_v [:: a] <= 2.
   rewrite spec_sorted_rec /= /Zval_v big_cons big_nil addn0.
   by rewrite leqn1; case/andP; case/orP => /eqP ->; rewrite ?v0 ?v1.
move: (v_exists 4) => [l].
  case:l; [by rewrite Hd | move => a4]; case; last move => b4.
    by move/He => h1 h2; move: h1; rewrite h2. 
  case; last by move => c4 l /Hc => h1 h2; move: h1; rewrite h2. 
move: (v_exists 5) => [l].
  case:l; [by rewrite Hd | move => a5]; case; last move => b5.
    by move/He => h1 h2; move: h1; rewrite h2. 
  case; last by move => c4 l /Hc => h1 h2; move: h1; rewrite h2. 
rewrite !spec_sorted_rec /spec_sorted /= ! andbT.
rewrite /Zval_v !big_cons !big_nil !addn0 => /andP [pa pb] pc /andP [pe pf] pg.
move:pb; rewrite leqn1;case/orP => /eqP eq1; move: pc; rewrite eq1; last first.
  rewrite v1 addn1 => /eqP; rewrite eqSS => /eqP va5. 
  move: pf; rewrite leqn1;case/orP => /eqP eq2; move: pg; rewrite eq2.
    rewrite v0; move => /eqP; rewrite addn2 eqSS eqSS - v0=> /eqP /DUR_injv.
    by move => ba; move: pe;rewrite eq2 ba //.
  rewrite v1 addn1 => /eqP; rewrite eqSS => /eqP va4; rewrite eq2 in pe.
  rewrite eq1 in pa; case/orP: pa => /eqP ea;  case/orP: pe => /eqP eb.
  + by move: va5 va4; rewrite ea eb => ->.
  + by move:(DUR_exclusion1 1); rewrite v1 - eb va4 - {2} ea va5 //.
  + by move:(DUR_exclusion2 0); rewrite - {1} ea - {1} eb v0 v1 va4 va5.
  + by move: va5 va4; rewrite ea eb => ->.
rewrite v0 addn2 => /eqP; rewrite !eqSS => /eqP va5.
move: pa va5; rewrite eq1; case /orP => /eqP ->;first by rewrite v1 //.
move => v2; clear a4 b4 a5 b5 pe pf pg eq1.
have Hf: v 3 != 4. 
  by apply/negP => /eqP v3; move:(DUR_exclusion2 0); rewrite v0 v1 v2 v3.
have Hg i: 3 <= i -> 4 <= v i.
   move=> ha;rewrite !ltn_neqAle; case: eqP.
     by rewrite - v2; move/DUR_injv => h; move: ha; rewrite h ltnn.
  case: eqP; first by rewrite - v0; move/DUR_injv => h; move: ha; rewrite -h.
  case: eqP; first by rewrite -v1;move/DUR_injv => h; move: ha; rewrite -h. 
  by rewrite eq_sym (lt0n_neq0 (DUR_positive i)).
have Hi a b c d l: spec_sorted [:: a, b, c, d & l] ->
   10 <= Zval_v [:: a, b, c, d & l]. 
  move => H; move:(H).
  move => /spec_sorted_sorted /= /andP [lta /andP [ltb /andP [ltc _]]].
  have w: 3 <= d.+3 by [].
  rewrite - 2!ltnS in ltc; rewrite - ltnS in ltb.
  move: (leq_trans w (leq_trans (leq_trans ltc ltb) lta)) => /Hg la.
  move: H; rewrite spec_sorted_rec => /= /andP [_ /Hc] lb.
  rewrite /Zval_v (big_cons); exact:(leq_add la lb).
move:(v_exists 7) => [l]. 
case:l; [by rewrite Hd | move => a7]; case.
  by move/He => h1 h2; move: h1; rewrite h2. 
move => b7; case; last first.  
  have Hj i: 3 < i ->  v i + v 3 == 6  -> False.
    move => ha hb. 
    by move: (leq_add (Hg _ (ltnW ha)) (Hg 3 (leqnn 3))); rewrite (eqP hb).
  move => c7; case; last by move => a l /Hi => h1 h2; move: h1; rewrite h2.
  rewrite !spec_sorted_rec /spec_sorted /= ! andbT.
  rewrite /Zval_v !big_cons big_nil addn0 leqn1. 
  case/and3P; case/orP => /eqP ea; case/orP => /eqP eb; case/orP => /eqP ec;
    rewrite ea eb ec ?v0 ?v1 ?v2 => /eqP.
  + done.
  + by rewrite -[7]/(3 + (3 +1)) (eqn_add2r) -{2} v2 => /eqP/DUR_injv.
  + by rewrite -[7]/(2 + (3 +2)) (eqn_add2r) -{2} v0  => /eqP/DUR_injv.
  + by rewrite addnA addn1 eqSS => /(Hj _ (leqnn 4)).
  + by rewrite -[7]/(4 + (1 +2)) (eqn_add2r) => ha; move: Hf; rewrite ha.
  + by rewrite -[7]/(3 + (3 +1)) (eqn_add2r)  -{2} v2 => /eqP/DUR_injv.
  + by rewrite -[7]/(2 + (3 +2)) (eqn_add2r)  -{2} v0 => /eqP/DUR_injv.
  + by rewrite addnA addn1 eqSS => /(Hj _ (ltnW (leqnn 5))).
rewrite !spec_sorted_rec /spec_sorted /= ! andbT.
rewrite /Zval_v !big_cons big_nil addn0 leqn1. 
case/andP; case/orP => /eqP sa; case/orP => /eqP sb;
    rewrite sa sb ? v0 ? v1 ? v2 // => /eqP; rewrite addn1 eqSS => /eqP v3.
clear a7 b7 sa sb.
move:(v_exists 8) => [l]. 
case:l; [by rewrite Hd | move => a8]; case.
  by move/He => h1 h2; move: h1; rewrite h2. 
move => b8; case.
  rewrite !spec_sorted_rec /spec_sorted /= ! andbT.
  rewrite /Zval_v !big_cons big_nil addn0 leqn1.
  case/andP; case/orP => /eqP sa; case/orP => /eqP sb;
    rewrite sa sb ? v0 ? v1 ? v2 // => /eqP; rewrite addn1 eqSS v3 //.
move => c8; case; last by move => a l /Hi => h1 h2; move: h1; rewrite h2.
rewrite !spec_sorted_rec /spec_sorted /= ! andbT.
rewrite /Zval_v !big_cons big_nil addn0 leqn1. 
case/and3P; case/orP => /eqP ea; case/orP => /eqP eb; case/orP => /eqP ec;
    rewrite ea eb ec ?v0 ?v1 ?v2 ?v3 => /eqP //.
+ by rewrite -[8]/(1 + (6 +1)) (eqn_add2r) -{2} v1 => /eqP/DUR_injv.
+ rewrite -[8]/(4 + (3 +1)) (eqn_add2r) => /eqP v4.
  by move:(DUR_exclusion2 1); rewrite v1 v2 v3 v4.
+ by rewrite -[8]/(3 + (3 +2)) (eqn_add2r) -{2} v2 => /eqP/DUR_injv.
+ by rewrite -[8]/(1 + (6 +1)) (eqn_add2r) -{2} v1 => /eqP/DUR_injv.
Qed.

Lemma DUR_fib i : v i = fib i.+2.
Proof.
move:i.
have Ha l i a: i \in a :: l -> path gtn a l -> i <= a.
  rewrite inE; case/orP; first by move /eqP => ->.
  elim:l i a => // a l H i b /= h /andP [ha hb]; move:h;  rewrite inE.
  case/orP; [ by move/eqP ->; apply: ltnW |move => il;apply:H => //].
  move: ha hb; case l => // a' l' /= ha /andP [hb ->]. 
  by rewrite (ltn_trans hb ha).
have Hb  k: (forall i, i < k.*2 -> v i = fib i.+2) ->
   (v k.*2.+1 < fib k.*2.+1 \/ 
      (v k.*2 = fib k.*2.+2 /\ v k.*2.+1 < fib k.*2.+3)) -> False.
  move => Hrec lta;case /andP: (max_rep_fib2 k.+1).
  case/andP: (max_rep_fib2 k); set l' := rev _; set l := rev _.
  move => _ /eqP zvl' ssl /eqP zvl.
  have lt1:v k.*2.+1 < fib k.*2.+3.
    case: lta; last by case. 
    move =>h;apply: (leq_trans h); by apply: fib_monotone;apply: ltnW => //.
  have lv: l = k.*2.+1 :: l'.
     rewrite /l /l' /mkseq iota_Sr /succ_seq - !map_comp /comp - !map_rev.
     by rewrite rev_rcons.
  set s :=  \sum_(i <- l) v i; set s' := Zeck_val l.
  have eqr: \sum_(i <- l') v i = Zeck_val l'.
    rewrite /Zeck_val /l' ! sum_rev /mkseq /succ_seq !big_map.
    apply: eq_big_seq => i; rewrite mem_iota /= add0n => ik.
    by apply: Hrec; rewrite ltn_Sdouble.
  move: (ZeckM_prop2 s); set z := ZeckM s; move /andP => [ssz /eqP].
  move: ssz; case:z. 
    rewrite Zeckv_nil /s lv big_cons => _ /eqP; rewrite eq_sym addn_eq0.
    by move/andP => [/eqP h _]; move:(DUR_positive k.*2.+1); rewrite h.
  move => hz tz ssz zv.
  move:(max_rep_bound ssz); rewrite zv; move => /andP [le2 _ ].
  have: s < s' by rewrite /s/s' lv Zeckv_cons big_cons eqr ltn_add2r. 
  move/(leq_ltn_trans le2); rewrite /s' zvl - ltnS - fib_pos // - fib_pos //.
  move/fib_monotone_bis; rewrite doubleS !ltnS => hm.
  suff Hz: forall i, i <= hz -> v i = fib i.+2.
    have eq2: Zval_v (hz :: tz) = Zval_v l.
      rewrite -[RHS] zv /Zeck_val /Zval_v;apply: eq_big_seq => i il.
      exact (Hz _ (Ha _ _ _ il (spec_sorted_sorted ssz))).
    move:(v_unique ssz ssl eq2);rewrite lv; case => eq3.
    by move: hm; rewrite eq3 ltnn.
  case: lta; last first.
    move => [pa pb] i li; move: (leq_trans li hm); rewrite leq_eqVlt.
    by case/orP; [ move/eqP => -> // | apply/ Hrec ].
  move => la.
  have: s < (fib k.*2.+3).-1. 
    rewrite /s lv big_cons eqr zvl' (fibSS k.*2.+1) {2} (fib_pos k.*2.+1). 
    by rewrite addSn addnC ltn_add2l.
  move/(leq_ltn_trans le2); rewrite - ltnS - fib_pos //- fib_pos //.
  move/fib_monotone_bis;rewrite  !ltnS => hm1 i ih; apply: Hrec.
  apply: (leq_ltn_trans ih hm1). 
have Hc k: (forall i, i < k.*2.+1 -> v i = fib i.+2) ->
   (v k.*2.+2 < fib k.*2.+2 \/ 
      (v k.*2.+1 = fib k.*2.+3 /\ v k.*2.+2 < fib k.*2.+4)) -> False.
  move => Hrec lta; case /andP: (max_rep_fib1 k.+2).
  case /andP: (max_rep_fib1 k.+1); set l' := rev _; set l := rev _.
  move => _ /eqP zl' ssl /eqP zvl.
  have lv: l = k.+1.*2 :: l' by rewrite /l/l'/mkseq iota_Sr -!map_rev rev_rcons.
  set s := \sum_(i <- l) v i; set s' := Zeck_val l.
  have lt1:v k.*2.+2 < fib k.*2.+4.
    case: lta; last by case. 
    move =>h;apply: (leq_trans h); by apply: fib_monotone;apply: ltnW => //.
   have eqr: \sum_(i <- l') v i = Zeck_val l'.
    rewrite /Zeck_val /l' ! sum_rev /mkseq /succ_seq !big_map.
    apply: eq_big_seq => i; rewrite mem_iota /= add0n => ik.
    by apply: Hrec; rewrite ltnS leq_double - ltnS.
  move: (ZeckM_prop2 s); set z := ZeckM s; move /andP => [ssz /eqP].
  move: ssz; case:z. 
    rewrite Zeckv_nil /s lv big_cons => _ /eqP; rewrite eq_sym addn_eq0.
    by move/andP => [/eqP h _]; move:(DUR_positive (k.+1).*2); rewrite h.
  move => hz tz ssz zv.
  move:(max_rep_bound ssz); rewrite zv; move => /andP [le2 _ ].
  have: s < s' by rewrite /s/s' lv Zeckv_cons big_cons eqr ltn_add2r.
  move/(leq_ltn_trans le2); rewrite /s' zvl - ltnS - fib_pos // - fib_pos //.
  move/fib_monotone_bis; rewrite doubleS 3!ltnS => hm.
  suff Hz: forall i, i <= hz -> v i = fib i.+2.
    have eq2: Zval_v (hz :: tz) = Zval_v l.
      rewrite -[RHS] zv /Zeck_val /Zval_v;apply: eq_big_seq => i il.
      exact (Hz _ (Ha _ _ _ il (spec_sorted_sorted ssz))).
    move:(v_unique ssz ssl eq2);rewrite lv; case => eq3.
    by move: hm; rewrite eq3 ltnn.
  case: lta; last first.
    move => [pa pb] i li; move: (leq_trans li hm); rewrite leq_eqVlt.
    by case/orP; [ move/eqP => -> // | apply/ Hrec ].
  move => la.
  have: s < (fib k.*2.+4).-1. 
    rewrite /s lv big_cons eqr zl' (fibSS k.*2.+2) {2} (fib_pos k.*2.+2). 
    by rewrite addSn addnC ltn_add2l.
  move/(leq_ltn_trans le2); rewrite - ltnS - fib_pos //- fib_pos //.
  move/fib_monotone_bis;rewrite  !ltnS => hm1 i ih; apply: Hrec.
  by rewrite ltnS (leq_trans ih hm1). 
have Hj a l: spec_sorted l -> a \in l -> exists w L,
    spec_sorted (a :: L) /\ l = w ++  (a :: L).
  elim: l a => [ a // | b l H a ha]. 
  rewrite inE; case/orP; first by by move => /eqP ->; exists nil, l. 
  move: ha; rewrite spec_sorted_rec => /andP[_] ha hb; move:(H _ ha hb).
  by move => [w [L [hc ->]]]; exists (b::w), L.
move => i. 
move:DUR_01 =>[v0 v1].
elim: i {-2} i (leqnn i); first by move => i; rewrite leqn0 => /eqP -> //.
move => n Hrec n1; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: Hrec; rewrite -ltnS.
move/eqP ->; clear n1.
case: (ltngtP (v n.+1)(fib n.+3)) => // lt1.
  case: (odd_dichot n.+1); set k := (n.+1)./2 => nv.
    move: nv => /eqP;rewrite eqSS => /eqP nv; case: (Hb k).
      by rewrite - nv; move => i /ltnW /Hrec.
    by right; rewrite - nv; split => //; apply: Hrec.
  have nv2: n = (k.-1).*2.+1.
     by move: nv; case:k => // k /= /eqP; rewrite doubleS eqSS => /eqP.
  case: (Hc k.-1).
    by move => i; rewrite -nv2 => /ltnW/Hrec.
  by right; rewrite - nv2; split => //; apply: Hrec.
move: lt1;case: (ltngtP (fib n.+3) (v n.+1)) => // lt2 _.
move:(fib_sum_alt n.+1); rewrite - Zeckv_rev; set l := rev (iota 0 n.+1) => xm1.
have eq2: Zval_v l = Zeck_val l.
  rewrite /Zeck_val /Zval_v; apply: eq_big_seq => i il; apply/ Hrec.
  by move: il; rewrite /l mem_rev mem_iota /= ltnS.
set x := (Zval_v l).+1; move: (v_exists x) => [L].
case:L =>[ |a L ss sv]; first by rewrite/Zval_v big_nil /x.
have Hi k: (fib k.+4).-2.+2 = fib k.+4.
  have:  fib 3 < fib k.+4 by apply:fib_smonotone_bis.
  by move/ltnW /subnK; rewrite subn2 addn2.
case: (leqP a n) => can.
  have eq1: Zval_v (a :: L) = Zeck_val (a :: L).
    rewrite /Zeck_val /Zval_v; apply: eq_big_seq => i il.
    move:(leq_trans (Ha _ _ _ il (spec_sorted_sorted ss)) can); apply: Hrec.
  move: (max_rep_bound ss); rewrite - eq1 sv /x eq2 xm1. 
  move /andP => [_]. rewrite - ltnS Hi - fib_pos => /fib_monotone_bis.
  by rewrite !ltnS ltnNge can.
case nl: (n.+1 \in (a::L)).
  move:(Hj _ _ ss nl) => [w [l1 [sl1 l1v]]].
  have eq3: \sum_(j <- l1) v j = Zeck_val l1.
    rewrite /Zeck_val; apply: eq_big_seq => i.
    move: sl1; rewrite spec_sorted_rec; case/andP =>[].
    case l1 => // b l2 /= pa pb pc; apply: Hrec.
    apply: (leq_trans (Ha _ _ _  pc (spec_sorted_sorted pb))).
    by move:pa; rewrite !eqSS; case/orP => /eqP ->.
  have lta: Zeck_val (n.+1::l1) <= (fib n.+4).-2.
    move: lt2; rewrite -(ltn_add2r ( Zeck_val l1));rewrite Zeckv_cons => h.
    rewrite - ltnS;apply: (leq_trans h); rewrite -xm1 - eq2 -eq3 -/x -sv. 
    by rewrite /Zval_v l1v big_cat big_cons/=; apply: leq_addl.
  move: (max_rep_bound sl1) => /andP [hh _].
  by move: (leq_trans hh lta);rewrite - {1} Hi /= ltnn.
case nl2: (n.+2 \in (a::L)); last first.
   move:(negbT nl2); move/negP; case; move: ss can nl; clear.
   elim: L a n.  
     move => a n;rewrite spec_sorted_rec /= => /andP[la1 _] na.  
     move:(leq_trans na la1); rewrite ltnS leqn0 => nz.
     by move: la1 na; rewrite (eqP  nz) inE; case a => //; case.
  move => a l Hrec b n; rewrite spec_sorted_rec /= => /andP[ha hb].
  rewrite inE leq_eqVlt; case: (n.+1 == b) => //=;rewrite  leq_eqVlt !inE. 
  case: (n.+2 == b) => //=; move => nb; apply: Hrec => //.
  by move: nb; case /orP: ha => /eqP -> // h; apply: ltnW.
move: (Hj _ _ ss nl2) => [w [l2 [sa sb]]].
move: nl; rewrite sb; rewrite mem_cat => /norP [_] nl.
move: sa sb nl; rewrite spec_sorted_rec; case: l2 => // b l2 /=.
rewrite !inE !eqSS => /andP []; case/orP; first by move => -> //=;rewrite orbT.
move => /eqP <- => pa pb _.
move: (max_rep_bound pa) => /andP [lt1 _].
have pc: \sum_(j <- (n :: l2)) v j = Zeck_val (n :: l2).
  rewrite /Zeck_val; apply: eq_big_seq => i il; apply: Hrec.
  exact: (Ha _ _ _  il (spec_sorted_sorted pa)).
move: sv; rewrite pb /Zval_v big_cat /= big_cons pc /x eq2 xm1 => sa.
move:(leq_addl (\sum_(i <- w) v i) (v n.+2 + Zeck_val (n :: l2))).
rewrite sa fibSS fib_pos addSn (fib_pos n.+1) addnS /= -addnS - fib_pos => lt3.
move: lt1; rewrite - (leq_add2r (fib n.+2)) => lt4.
move:(leq_trans lt3 lt4); rewrite addnC leq_add2l leq_eqVlt.
have W: forall k, k.+2 = k -> False by elim => // k H; case.
case: eqP; first by rewrite -(Hrec n (leqnn n)) => /DUR_injv // /W.
move => _ /= Hx.
case: (odd_dichot n.+2); set k := (n.+2)./2 => nv.
  move: nv => /eqP;rewrite eqSS => /eqP nv; case: (Hb k); rewrite - nv //.
  by left.
move: (Hc k.-1).
have  <-: n = (k.-1).*2.
  by move: nv; case:k => // k /= /eqP; rewrite doubleS !eqSS => /eqP.
by case => //; left.
Qed.

End  DualUniqueRepresentation.


(* -------------------------------------------------------- *)

(** The cardinal of the stuff *)



Definition seto_to_seq B (l: {set 'I_B.+1}) := 
  [seq (nat_of_ord i) | i <- enum l].


Definition seq_to_seto B l := 
  [set i | i in [seq (inord i : 'I_B.+1) | i <- l]].


Lemma seto_to_seqK B (s: {set 'I_B.+1}) : seq_to_seto B (seto_to_seq s) = s.
Proof.
rewrite /seq_to_seto/seto_to_seq - map_comp /comp.
apply/setP =>i; apply/imsetP/idP.
  by move => [x /mapP [y ]]; rewrite mem_enum inord_val => ys -> ->. 
move => h; rewrite - (inord_val i);exists (inord i) => //.
by apply: map_f; rewrite mem_enum.
Qed.


Lemma seq_to_setoK B (l:  seq nat): 
  uniq l -> (all (fun z => z < B.+1) l) ->
  perm_eq (seto_to_seq (seq_to_seto B l)) l.
Proof.
move => ul /allP bl.
rewrite /seq_to_seto/seto_to_seq.
apply: uniq_perm_eq => //.
   rewrite map_inj_uniq; [ apply: enum_uniq | apply: ord_inj].
move => x;  apply/mapP/idP.
  move=> [i]; rewrite mem_enum => /imsetP [j /mapP [k kl ->] ->] ->.
  by rewrite inordK //; apply: bl.
move => xl; exists (inord x); last by rewrite inordK //; apply: bl.
by rewrite mem_enum; apply /imsetP; exists (inord x) => //; apply: map_f.
Qed.

Lemma uniq_seto_to_seq B l: uniq (@seto_to_seq B l).
Proof. rewrite map_inj_uniq;[ exact: enum_uniq | exact:ord_inj]. Qed.

Lemma Zeckvp_bnd l i: i \in l -> i <= Zeck_valp l.
Proof.
elim: l i => // [a l Hrec i /=]; rewrite in_cons Zeckvp_cons; case/orP. 
   move /eqP => ->; case: a => // a.
   apply: (leq_trans ((fib_gen a.+1))); apply: leq_addr.
move/Hrec/leq_trans => -> //; exact:leq_addl.
Qed.

Lemma Zeckv_bnd0 l i: i \in l -> fib (i.+2) <= Zeck_val l.
Proof.
elim: l i => // [a l Hrec i /=]; rewrite in_cons Zeckv_cons; case/orP. 
   move /eqP => ->; case: a => // a; apply: leq_addr.
move/Hrec/leq_trans => -> //; exact:leq_addl.
Qed.

Lemma Zeckv_bnd l i: i \in l -> i <= Zeck_val l.
Proof. rewrite Zeck_valppE=> /Zeckvp_bnd/leq_trans -> //; exact: leq_addr. Qed.

Definition Zeck_sval B (t:{set 'I_B.+1}) := \sum_(i in t) (fib i.+2).
Definition Zeck_svalp B (t:{set 'I_B.+1}) := \sum_(i in t) (fib i.+1).

Lemma Zeck_val_cv0 B (t:{set 'I_B.+1}) (f:nat->nat):
  \sum_(i <- (seto_to_seq t)) f i =  \sum_(i in t) f i.
Proof.
transitivity (\sum_(i <- (enum t)) (f i)).
  rewrite /seto_to_seq /Zeck_val;elim (enum t); first by rewrite ! big_nil. 
  by move => a l h; rewrite map_cons !big_cons h.
rewrite -filter_index_enum big_filter_cond. 
by apply: eq_big =>//x; rewrite andbT.
Qed.

Lemma Zeck_val_cv1 B (t:{set 'I_B.+1}) :
  Zeck_val (seto_to_seq t) =  Zeck_sval t.
Proof. exact: Zeck_val_cv0. Qed.

Lemma Zeck_valp_cv1 B (t:{set 'I_B.+1}) :
   Zeck_valp (seto_to_seq t) =  Zeck_svalp t.
Proof. exact: Zeck_val_cv0. Qed.

Lemma Zeck_val_cv2 l B (n := Zeck_val l): uniq l -> n <= B ->
   n =  Zeck_sval (seq_to_seto B l).
Proof.
move => sa sb.
symmetry;rewrite - Zeck_val_cv1; apply: eq_big_perm; apply:(seq_to_setoK sa).
apply /allP => i /Zeckv_bnd lin; rewrite ltnS; apply: (leq_trans lin sb).
Qed.

Lemma Zeck_valp_cv2 l B (n := Zeck_valp l): uniq l -> n <= B ->
  n =  Zeck_svalp (seq_to_seto B l).
Proof.
move => sa sb.
symmetry;rewrite - Zeck_valp_cv1; apply: eq_big_perm; apply:(seq_to_setoK sa).
apply /allP => i /Zeckvp_bnd lin; rewrite ltnS; apply: (leq_trans lin sb).
Qed.


Definition GRr B n := #|[set t:{set 'I_B.+1} | Zeck_sval t == n ]|.
Definition GAr B m n := #|[set t:{set 'I_B.+1} | 
   (Zeck_svalp t == m) && (Zeck_sval t == n) ]|.

Definition GR n := GRr n n.
Definition GA m n := GAr n m n.

Lemma GARr_aux n B 
  (g: ({set 'I_n.+1} ->  {set 'I_B.+1})
     := (fun t => [set (inord (i:'I_n.+1)) | i in  t])):
  n <= B -> 
  (injective g /\ forall (t:{set 'I_n.+1}) (F: nat -> nat), 
     \sum_(i in t) F i= \sum_(i in (g t)) F i).
Proof.
rewrite -ltnS => lenB.
set f: ('I_n.+1 ->  'I_B.+1) := fun i => inord i.
pose Hw x := (inordK (leq_trans (ltn_ord x) lenB)).
have Ha: injective f.
   move => i j; rewrite /f => sa.
   move:(f_equal (@nat_of_ord B.+1) sa); rewrite (Hw i) (Hw j); apply:ord_inj.
split.
  rewrite /g => x y si; apply /setP => i; apply/idP/idP => ha.
     have: (f i) \in  [set f i | i in x] by apply/imsetP; exists i.
     by rewrite si => /imsetP [t ty /Ha ->].
  have: (f i) \in  [set f i | i in y] by apply/imsetP; exists i.
  by rewrite - si => /imsetP [t ty /Ha ->]. 
move => t F.
rewrite - (Zeck_val_cv0 t) - (Zeck_val_cv0 (g t)).
apply: eq_big_perm; apply: uniq_perm_eq.
+ rewrite map_inj_uniq; [ apply: enum_uniq | apply: ord_inj].
+ rewrite map_inj_uniq; [ apply: enum_uniq | apply: ord_inj].
+ rewrite /seto_to_seq => i; rewrite /g;apply /mapP/idP.
    move => [x]; rewrite mem_enum => xt ->. 
    by rewrite -(Hw x) map_f // mem_enum; apply /imsetP; exists x.
  move/mapP => [j];rewrite mem_enum; move/imsetP => [k kt -> ->].
  by apply/mapP; rewrite (Hw k) map_f // mem_enum.
Qed.

Lemma GRr_big0 A B n: n < fib A.+3 -> A <= B -> GRr A n = GRr B n.
Proof.
rewrite /GRr => ns lenm.
move:(GARr_aux lenm); set g := (fun t:_ => _); move => [Hb Hx].
move:lenm; rewrite - ltnS => lenm.
pose Hw x := (inordK (leq_trans (ltn_ord x) lenm)).
have Hc: forall t, Zeck_sval t =  Zeck_sval (g t).
  move => t; apply: (Hx t (fun z => (fib z.+2))).
set pn := [pred t : {set 'I_A.+1} | Zeck_sval t == n].
rewrite cardsE -(card_imset pn Hb).
apply: eq_card => e; rewrite inE; apply/imsetP/idP.
  by move => [x]; rewrite  inE Hc => ww ->.
set l :=(seq_to_seto A (seto_to_seq e)) => eq.
suff ww : e = g l by exists l => //; rewrite /pn inE Hc - ww.
have Hd: forall i, i \in e -> i <= A.
  move => i ie.
  rewrite - 3!ltnS; apply:fib_monotone_bis; apply: leq_trans ns. 
   rewrite ltnS -(eqP eq) - Zeck_val_cv1.
   by apply:Zeckv_bnd0; rewrite  /seto_to_seq map_f // mem_enum.
rewrite /l /g /seq_to_seto/seto_to_seq - map_comp /comp.
apply/setP =>i; apply/idP/imsetP.
  move => ie;  move:(inordK (Hd _ ie)) => sa.
  rewrite - mem_enum in ie; exists (inord i); last by rewrite sa inord_val. 
  by apply /imsetP;  exists (inord i) => //;rewrite (map_f _ ie).
move => [j /imsetP [k /mapP [x]]];rewrite mem_enum => H.
by move => -> -> -> /=; rewrite inordK ? inord_val // ltnS Hd.
Qed.

Lemma GAr_big0 A B m n:  ((m < fib A.+2) || (n < fib A.+3)) -> A <= B -> 
    GAr A m n = GAr B m n.
Proof.
rewrite /GRr => ns lenm.
move:(GARr_aux lenm); set g := (fun t:_ => _); move => [Hb Hx].
move:lenm; rewrite - ltnS => lenm.
have HB0 l i: i \in l -> fib (i.+1) <= Zeck_valp l.
  elim: l i => // [a l Hrec i /=]; rewrite in_cons Zeckvp_cons; case/orP. 
     move /eqP => ->; case: a => // a; apply: leq_addr.
  move/Hrec/leq_trans => -> //; exact:leq_addl.
pose Hw x := (inordK (leq_trans (ltn_ord x) lenm)).
have Hc1: forall t, Zeck_sval t =  Zeck_sval (g t).
  move => t; apply: (Hx t (fun z => (fib z.+2))).
have Hc2: forall t, Zeck_svalp t =  Zeck_svalp (g t).
  move => t; apply: (Hx t (fun z => (fib z.+1))). 
set pn := [pred t : {set 'I_A.+1} | Zeck_svalp t == m & Zeck_sval t == n].
rewrite /GAr cardsE -(card_imset pn Hb).
apply: eq_card => e; rewrite inE; apply/imsetP/idP.
  by move => [x]; rewrite  inE Hc1 Hc2 => ww ->.
set l :=(seq_to_seto A (seto_to_seq e)) => eqa.
move: (eqa) => /andP[/eqP eqb /eqP eqc].
suff ww : e = g l by exists l => //; rewrite /pn inE Hc1 Hc2 - ww.
have Hd: forall i, i \in e -> i <= A.
  move => i ie.
  have ie': (nat_of_ord i) \in  (seto_to_seq e).
    by rewrite  /seto_to_seq map_f // mem_enum. 
  move: (Zeckv_bnd0 ie')(HB0 _ _ ie').
  rewrite Zeck_val_cv1  Zeck_valp_cv1 eqb eqc => la lb; case/orP: ns => lc.
    by move: (leq_ltn_trans lb lc) => /fib_monotone_bis; rewrite !ltnS.
  by move: (leq_ltn_trans la lc) => /fib_monotone_bis; rewrite !ltnS.
rewrite /l /g /seq_to_seto/seto_to_seq - map_comp /comp.
apply/setP =>i; apply/idP/imsetP.
  move => ie;  move:(inordK (Hd _ ie)) => sa.
  rewrite - mem_enum in ie; exists (inord i); last by rewrite sa inord_val. 
  by apply /imsetP;  exists (inord i) => //;rewrite (map_f _ ie).
move => [j /imsetP [k /mapP [x]]];rewrite mem_enum => H.
by move => -> -> -> /=; rewrite inordK ? inord_val // ltnS Hd.
Qed.

Lemma GRr_big B n: n <= B -> GRr B n = GR n.
Proof.
rewrite /GR => lnb; symmetry; apply:GRr_big0 => //.
by apply: leq_trans (fib_gen n.+2).
Qed.


Lemma GAr_big B m n: n <= B -> GAr B m n = GA m n.
Proof.
rewrite /GA => lnb; symmetry; apply:GAr_big0 => //.
by rewrite  (leq_ltn_trans  (leqnSn n)(fib_gen n.+2)) orbT.
Qed.
 
Lemma GAr_notz B m n: GAr B m n!= 0 -> m = Zeckp n.
Proof.
rewrite /GAr cards_eq0 => /set0Pn [x ];rewrite inE => /andP [/eqP pa /eqP pb].
move:(Zeck_val_cv1 x) (Zeck_valp_cv1 x); rewrite - pa - pb  => <- <-.
symmetry; apply: Zeckp_prop1; apply:uniq_seto_to_seq.
Qed.

Lemma GARr_e B n: GAr B (Zeckp n) n = GRr B n.
Proof.
rewrite /GAr/GRr; apply: eq_card => e; apply /idP/idP;rewrite !inE.
  by move/andP => [].
move => /eqP <-; rewrite  eqxx andbT  - Zeck_val_cv1 - Zeck_valp_cv1. 
apply/eqP; symmetry; apply: Zeckp_prop1;  apply:uniq_seto_to_seq.
Qed.

Lemma GAR_e n: GA (Zeckp n) n = GR n.
Proof. exact:GARr_e. Qed.

Lemma GRr_notz B n: fib B.+4 <= n.+1 -> GRr B n = 0.
Proof.
suff: GRr B n != 0 -> n.+2 <= fib B.+4.
 by move/contraR; rewrite -leqNgt => h h1; apply/eqP/h.
rewrite cards_eq0 => /set0Pn [x ];rewrite inE => /eqP pa.
rewrite -pa -(Zeck_val_cv1 x). apply: (Zeckv_bound3 (uniq_seto_to_seq x)).
by apply/allP => i /mapP [j _ ->];case:j.
Qed.

Lemma GRr_b0 B:  GRr B 0 = 1.
Proof.
rewrite /GRr; set E :=  [set t | _];set v := (@set0 ( (ordinal_finType B.+1))).
suff: [set v] = E by move => <-; rewrite cards1.
apply/ setP => x; rewrite !inE - Zeck_val_cv1; apply/eqP/eqP => h. 
  by rewrite h /seto_to_seq enum_set0 /= Zeckv_nil.
case ee: (x==v); [by apply/eqP |move:(negbT ee) ]. 
move/set0Pn => [u]; rewrite - mem_enum - (mem_map (@ord_inj B.+1)). 
move: h; rewrite -/(seto_to_seq _ ); case (seto_to_seq x) => // a l bad.
by move: (Zeckv_pos a l); rewrite bad.
Qed.

Lemma GRr_b1 B:  GRr B 1 = 1.
Proof.
rewrite /GRr; set E :=  [set t | _];set v := [set (@ord0 B) ].
suff: [set v] = E by move => <-; rewrite cards1.
apply/ setP => x; rewrite !inE - Zeck_val_cv1; apply/eqP/eqP => h. 
  by rewrite h /v /seto_to_seq enum_set1 /= Zeckv_cons Zeckv_nil.
have eqa: (seto_to_seq x)  = [::0].
  move: h; case: (seto_to_seq x); first by rewrite Zeckv_nil.
  move => a l; rewrite Zeckv_cons; case: a.
    rewrite /fib/= addn0 - {2}(addn0 1) => /eqP; rewrite eqSS; case: l => //.
    by move => b l /eqP h; move:(Zeckv_pos b l); rewrite h.
  move => n. 
  move:(leq0n n); rewrite - ltnS => /fib_smonotone_bis => h1 h2.
  by move: (leq_trans h1 (leq_addr (Zeck_val l) (fib n.+3))); rewrite h2.
rewrite - (seto_to_seqK x) eqa /seq_to_seto /v /=.
move: (inord_val (@ord0 B)) => /= eqb.
apply/setP => i; rewrite inE eqb; apply/imsetP/eqP. 
  by move=> [y ]; rewrite inE => /eqP ea ->.
by move => ->; exists ord0. 
Qed.

Lemma GRr_0n n:  GRr 0 n = (n<=1).
Proof.
move: (@GRr_notz 0 n);rewrite !ltnS; case: n; first by rewrite GRr_b0.
by case; [ by rewrite GRr_b1 | move => n]; rewrite !ltnS ltn0; apply.
Qed.

Lemma GRr_Sbn B n : 
  GRr B.+1 n =  GRr B n + (GRr B (n- fib(B.+3))) * (fib(B.+3) <= n).
Proof.
case: (ltnP n (fib B.+3)).
  by rewrite muln0 addn0 => le1; rewrite - (GRr_big0 le1 (leqnSn B)).
set b := (@ord_max B.+1).
rewrite muln1 addnC /GRr => eq1. 
set E := [set t | Zeck_sval t == n].
have hb: forall (p: (pred {set 'I_B.+2})),
 #|[pred x | x \in p & x \in E]| =
 #|[set t | (p t) && (Zeck_sval t == n) ]|.
  by move => p; rewrite cardsE;apply: eq_card => x; rewrite !inE.
set p := [pred t:{set 'I_B.+2} | b \in t].
have ha: #|[predI E & p]| = #|[pred x | (mem p) x &  (mem E) x]|. 
   by apply: eq_card => x; exact: andbC.
move:(GARr_aux (leqnSn B)); set g := (fun t: _ => _); move => [ig aux].
have ig2: forall (t : {set 'I_B.+1}), Zeck_sval t = Zeck_sval (g t).
  move => t; rewrite/Zeck_sval; apply: (aux t (fun i => fib i.+2)).
have gpn: forall x, b \notin (g x).
  move => x;  apply/imsetP => [[w _ eq2]]; have hc:= (ltn_ord w).
  move:(inordK (leq_trans hc (leqnSn B.+1))); rewrite - eq2.
  by apply/eqP/negbT; apply:gtn_eqF. 
rewrite - (cardID p) ha hb hb; congr addn; symmetry;last first.
  set pn := [pred t : {set 'I_B.+1} | Zeck_sval t == n].
  rewrite cardsE -(card_imset pn ig).
  apply: eq_card => e; rewrite inE; apply/imsetP/idP.
    move => [x]; rewrite inE ig2 => ww ->;rewrite ww andbT; apply: gpn.
  move/andP => [hc hd].
  have Hd: forall i, i \in e -> i <= B.
    move => i ie; have:= (ltn_ord i); rewrite ltnS leq_eqVlt; case/orP => // eb.
    have he: i = b by apply: ord_inj; rewrite (eqP eb) //.
    by move: hc; rewrite /p he !inE - he ie.
  set l :=(seq_to_seto B (seto_to_seq e)). 
  suff ww : e = g l by exists l => //; rewrite /pn inE ig2 - ww.
  rewrite /l /g /seq_to_seto/seto_to_seq - map_comp /comp.
  apply/setP =>i; apply/idP/imsetP.
    move => ie;  move:(inordK (Hd _ ie)) => sa.
    rewrite - mem_enum in ie; exists (inord i); last by rewrite sa inord_val. 
    by apply /imsetP;  exists (inord i) => //;rewrite (map_f _ ie).
  move => [j /imsetP [k /mapP [x]]];rewrite mem_enum => H.
  by move => -> -> -> /=; rewrite inordK ? inord_val // ltnS Hd.
set pn := [pred t : {set 'I_B.+1} | Zeck_sval t == n- fib B.+3].
pose g1 t := b |: g t. 
have hc: forall t, p (g1 t) by move => t; apply/setU11. 
have ig1: injective g1.
  move => t1 t2; rewrite /g1 => w; apply: ig.
  by rewrite - (setU1K (gpn t1)) w (setU1K (gpn t2)).
rewrite cardsE -(card_imset pn ig1).
have ig2': forall t, fib B.+3 + Zeck_sval t = Zeck_sval (g1 t).
  by move => t; rewrite ig2 / Zeck_sval /g1 big_setU1.
apply: eq_card => e; rewrite inE; apply/imsetP/idP.
    move => [x]; rewrite inE => /eqP sa sb.
  by rewrite sb hc - (subnK eq1) - sa addnC ig2' eqxx.
move/andP => [hc1 hd2]. 
set e1 := e :\ b.
have Hd: forall i, i \in e1 -> i <= B.
  move => i /setD1P[ib ie]. 
  have:= (ltn_ord i); rewrite ltnS leq_eqVlt; case/orP => // eb.
  by case/negP:ib; apply/eqP /ord_inj; rewrite (eqP eb).
set l :=(seq_to_seto B (seto_to_seq e1)). 
suff ww : e = g1 l. 
  exists l => //; rewrite /pn inE.
  by move: ww; rewrite - (eqP hd2) => ->; rewrite - ig2' addKn.
rewrite /l /g1 /seq_to_seto/seto_to_seq - map_comp /comp.
rewrite - {1} (setD1K hc1); congr setU. 
apply/setP =>i; apply/idP/imsetP. 
  move => ie;  move:(inordK (Hd _ ie)) => sa.
  rewrite - mem_enum in ie; exists (inord i); last by rewrite sa inord_val.
  by apply /imsetP;  exists (inord i) => //;rewrite (map_f _ ie).
move => [j /imsetP [k /mapP [x]]];rewrite mem_enum => H.
by move => -> -> -> /=; rewrite inordK ? inord_val // ltnS Hd.
Qed.


Lemma GAr_Sbn B m n: 
  GAr B.+1 m n =  GAr B m n + 
    (GAr B (m - fib (B.+2)) (n- fib(B.+3))) 
    * (fib(B.+3) <= n) * (fib(B.+2) <= m).
Proof.
set b := (@ord_max B.+1). 
case: (ltnP n (fib B.+3)).
  rewrite muln0 addn0 => le1. 
  have ha: (m < fib B.+2) || (n < fib B.+3) by rewrite le1 orbT.
  by rewrite -(GAr_big0 ha (leqnSn B)).
case: (ltnP m (fib B.+2)).
  rewrite muln0 addn0 => le1 le2. 
  have ha: (m < fib B.+2) || (n < fib B.+3) by rewrite le1.
  by rewrite -(GAr_big0 ha (leqnSn B)).
rewrite !muln1 addnC /GAr => leqfm leqfn. 
set E := [set t | _].
have hb: forall (p: (pred {set 'I_B.+2})),
 #|[pred x | x \in p & x \in E]| =
 #|[set t | (p t) && ((Zeck_svalp t == m) && (Zeck_sval t == n)) ]|.
  by move => p; rewrite cardsE;apply: eq_card => x; rewrite !inE.
set p := [pred t:{set 'I_B.+2} | b \in t].
have ha: #|[predI E & p]| = #|[pred x | (mem p) x &  (mem E) x]|. 
   by apply: eq_card => x; exact: andbC.
move:(GARr_aux (leqnSn B)); set g := (fun t: _ => _); move => [ig aux].
have ig2: forall (t : {set 'I_B.+1}), Zeck_sval t = Zeck_sval (g t).
  move => t; rewrite/Zeck_sval; apply: (aux t (fun i => fib i.+2)).
have ig2': forall (t : {set 'I_B.+1}), Zeck_svalp t = Zeck_svalp (g t).
  move => t; rewrite/Zeck_sval; apply: (aux t (fun i => fib i.+1)).
have gpn: forall x, b \notin (g x).
  move => x;  apply/imsetP => [[w _ eq2]]; have hc:= (ltn_ord w).
  move:(inordK (leq_trans hc (leqnSn B.+1))); rewrite - eq2.
  by apply/eqP/negbT; apply:gtn_eqF. 
rewrite - (cardID p) ha hb hb; congr addn; symmetry;last first.
  set pn := [pred t : {set 'I_B.+1} |(Zeck_svalp t == m) && (Zeck_sval t == n)].
  rewrite cardsE -(card_imset pn ig).
  apply: eq_card => e; rewrite inE; apply/imsetP/idP.
    move => [x]; rewrite inE ig2 ig2' => ww ->;rewrite ww andbT; apply: gpn.
  move/andP => [hc hd].
  have Hd: forall i, i \in e -> i <= B.
    move => i ie; have:= (ltn_ord i); rewrite ltnS leq_eqVlt; case/orP => // eb.
    have he: i = b by apply: ord_inj; rewrite (eqP eb) //.
    by move: hc; rewrite /p he !inE - he ie.
  set l :=(seq_to_seto B (seto_to_seq e)). 
  suff ww : e = g l by exists l => //; rewrite /pn inE ig2 ig2' - ww.
  rewrite /l /g /seq_to_seto/seto_to_seq - map_comp /comp.
  apply/setP =>i; apply/idP/imsetP.
    move => ie;  move:(inordK (Hd _ ie)) => sa.
    rewrite - mem_enum in ie; exists (inord i); last by rewrite sa inord_val. 
    by apply /imsetP;  exists (inord i) => //;rewrite (map_f _ ie).
  move => [j /imsetP [k /mapP [x]]];rewrite mem_enum => H.
  by move => -> -> -> /=; rewrite inordK ? inord_val // ltnS Hd.
set pn := [pred t : {set 'I_B.+1} | Zeck_svalp t == m - fib B.+2 & 
   Zeck_sval t == n- fib B.+3].
pose g1 t := b |: g t. 
have hc: forall t, p (g1 t) by move => t; apply/setU11. 
have ig1: injective g1.
  move => t1 t2; rewrite /g1 => w; apply: ig.
  by rewrite - (setU1K (gpn t1)) w (setU1K (gpn t2)).
rewrite cardsE -(card_imset pn ig1).
have ig3: forall t, fib B.+3 + Zeck_sval t = Zeck_sval (g1 t).
  by move => t; rewrite ig2 / Zeck_sval /g1 big_setU1.
have ig3': forall t, fib B.+2 + Zeck_svalp t = Zeck_svalp (g1 t).
  by move => t; rewrite ig2' /Zeck_svalp /g1 big_setU1.
apply: eq_card => e; rewrite inE; apply/imsetP/idP.
    move => [x]; rewrite inE; move => /andP[/eqP sa1 /eqP sa2] sb.
  rewrite sb hc - (subnK leqfn)- (subnK leqfm) - sa1 - sa2 addnC ig3'.
  by rewrite addnC ig3 !eqxx.
move/and3P => [hc1 /eqP hd2 /eqP hd2'].
set e1 := e :\ b.
have Hd: forall i, i \in e1 -> i <= B.
  move => i /setD1P[ib ie]. 
  have:= (ltn_ord i); rewrite ltnS leq_eqVlt; case/orP => // eb.
  by case/negP:ib; apply/eqP /ord_inj; rewrite (eqP eb).
set l :=(seq_to_seto B (seto_to_seq e1)). 
suff ww : e = g1 l. 
  exists l => //; rewrite /pn inE.
  by move: ww; rewrite -hd2 - hd2' => ->; rewrite -ig3 - ig3' !addKn !eqxx.
rewrite /l /g1 /seq_to_seto/seto_to_seq - map_comp /comp.
rewrite - {1} (setD1K hc1); congr setU. 
apply/setP =>i; apply/idP/imsetP. 
  move => ie;  move:(inordK (Hd _ ie)) => sa.
  rewrite - mem_enum in ie; exists (inord i); last by rewrite sa inord_val.
  by apply /imsetP;  exists (inord i) => //;rewrite (map_f _ ie).
move => [j /imsetP [k /mapP [x]]];rewrite mem_enum => H.
by move => -> -> -> /=; rewrite inordK ? inord_val // ltnS Hd.
Qed.

Lemma GR_example: GR 10 = 2.
Proof.
have Ha n: GRr 1 n = (n <= 3).
  by rewrite GRr_Sbn !GRr_0n; case:n => [ | [| [ | [ | n]]]].
have ha: GRr 3 2 = 1 by rewrite -(@GRr_big0 1 3 2) // GRr_Sbn ! GRr_0n.
rewrite /GR; rewrite -(@GRr_big0 4 10 10) // GRr_Sbn muln1 ha GRr_Sbn muln1.
by rewrite (@GRr_notz 2 10) // GRr_Sbn ! Ha.
Qed.

Lemma FAx_00: GA 0 0 = 1.
Proof. by move:(GAR_e 0); rewrite Zeckp_0 /GR GRr_0n. Qed.

Lemma FAx_0S n: GA 0 n.+1 = 0.
Proof.
case w: (GAr n.+1 0 n.+1 == 0); first by rewrite /GA (eqP w).
by move: (GAr_notz (negbT w)) => /esym/eqP;rewrite Zeckp_eq0.
Qed.

Lemma FAx_small m n: n < m -> GA m n = 0.
Proof.
move => h.
case w: (GAr n m n == 0); first by rewrite /GA (eqP w).
move: (GAr_notz (negbT w)) => ha.
by move: h; rewrite (Zeckp_prop2 n) - ha ltnNge leq_addr.
Qed.

(*

Lemma FA_0S n:  FA 0 n.+1 = 0.
Lemma FA_small m n: n < m -> FA m n = 0.
Lemma FA_gen m n: FA m.+1 (m.+1+n) = FA n m.+1 + FA n m.



*)


(** -----------  *)

(* FA *)

Fixpoint FA_rec (m n k:nat) :=
  if k is k'.+1 then
    if (m==0) then (n==0): nat
    else if n < m then 0  else FA_rec (n-m) m k' + FA_rec (n - m) (m-1) k'
  else 0.

Definition FA m n := FA_rec m n (m+n).+1.
Definition FR n := FA (Zeckp n) n.

Lemma FA_00: FA 0 0 = 1.
Proof. by []. Qed.

Lemma FA_0S n:  FA 0 n.+1 = 0.
Proof.  by []. Qed.

Lemma FA_small m n: n < m -> FA m n = 0.
Proof. by rewrite /FA;case:m  => // m /= ->. Qed.

Lemma FA_gen m n: FA m.+1 (m.+1+n) = FA n m.+1 + FA n m.
Proof.
suff H: forall u v k1 k2, u + v < k1 -> u + v < k2 -> 
     FA_rec u v k1 = FA_rec u v k2.
  have ha: n + m.+1 < m.+1 + (m.+1 + n). 
    by rewrite addnC ltn_add2l addSn ltnS leq_addl.
  have hb: n + m.+1 < (n + m.+1).+1 by rewrite ltnSn.
  have hc: n + m < m.+1 + (m.+1 + n).
    by rewrite addSn ltnS addnA addnC leq_add2r leq_addr.
  have hd: n + m < (n + m).+1 by apply: ltnSn.
  rewrite /FA {1} /FA_rec addKn subn1 succnK ltnNge leq_addr.
  by rewrite - (H  n m.+1  _ _ ha hb) - (H  n m  _ _ hc hd). 
move => u v; move: {2 3 4} (u+v) (leqnn (u+v)) => k.
clear m n; elim: k u v.
  move => u v; rewrite leqn0 addn_eq0 => /andP [/eqP -> /eqP ->].
  case => // k1; case => //. 
move => n Hrec u v luv; case => // k1; case =>  // k2; rewrite !ltnS => la lb.
move: luv; case: u => // u; rewrite addSn ltnS /=.
case(ltnP v u.+1) => // luv l2.
have ha: v - u.+1 + u.+1 <= n by rewrite (subnK luv) (leq_trans _ l2)?leq_addl.
have hb: v - u.+1 + (u.+1 - 1) <= n. 
  by  apply: leq_trans ha;  rewrite leq_add2l leq_subr.
by rewrite /= (Hrec _ _ ha k1 k2 la lb) (Hrec _ _ hb k1 k2).
Qed.

Lemma FA_mm m: FA m.+1 m.+1 = FA 0 m.
Proof. by move:(FA_gen m 0); rewrite addn0 FA_0S => ->. Qed.

Lemma FA_mm' m: FA m m = ((m <=1):nat).
Proof. by case: m => //m; rewrite FA_mm;case m. Qed.

Lemma FA_nz m n:  FA m n != 0 -> m = Zeckp n.
Proof.
move: (leq_maxl m n)  (leq_maxr m n); set s := (maxn m n).
move:s => s; elim: s m n.
   by move => m n; rewrite !leqn0 => /eqP -> /eqP ->; rewrite Zeckp_0.
move => b Hr m n; case: (ltngtP m n); last first.
+ move => -> _ _; rewrite FA_mm'; case n; first by rewrite Zeckp_0.
  by move => k; rewrite ltnS leqn0; case: k => //; rewrite Zeckp_1.
+ by move/FA_small => ->.
+ move => lemn _; rewrite leq_eqVlt; case/orP=> [|]; last first.
    by rewrite ltnS => nn; apply: (Hr _ _  (leq_trans (ltnW lemn) nn) nn).
  move: lemn; case:m; first by move => _ /eqP ->; rewrite FA_0S.
  move => m lmn /eqP nv.
  have lta: m.+1 <= b by rewrite - ltnS -nv.
  have ltc: (n - m.+1) <= b by rewrite -ltnS (subnSK (ltnW lmn)) -nv leq_subr.
  rewrite - (subnKC (ltnW lmn)) FA_gen addn_eq0 negb_and => /orP; case.
   by  move /(Hr _ _ ltc  lta) => ->; rewrite(Zeckp_prop3a m.+1).
  by move /(Hr _ _ ltc  (ltnW lta)) => ->; rewrite (Zeckp_prop4a m.+1).
Qed.

Lemma FA_prop0 a b: Zeckp b = a.+1 -> FA a b = 0.
Proof.
move =>eq1; case eq2:(FA a b == 0); first by rewrite (eqP eq2).
by move: (FA_nz (negbT eq2)); rewrite eq1 => /n_Sn.
Qed.

Lemma FA_prop0bis a b: (Zeckp b).+1 = a -> FA a b = 0.
Proof.
move => eq1; case eq2:(FA a b == 0); first by rewrite (eqP eq2).
by move: (n_Sn (Zeckp b)); rewrite eq1 (FA_nz (negbT eq2)). 
Qed.

Lemma FR_0: FR 0 = 1.
Proof. by rewrite /FR Zeckp_0 FA_00. Qed.

Lemma FR_1: FR 1 = 1.
Proof. by rewrite /FR Zeckp_1 FA_mm'. Qed.

Lemma FR_rec n (e := Zeckp n): n != 0 -> FR n = FA(n -e) e + FA (n-e) e.-1.
Proof.
rewrite /FR/e -Zeckp_eq0 - lt0n => /prednK => eq.
move: (Zeckp_le n) => [/subnKC sa sb].
by move: (FA_gen (Zeckp n).-1 (n - Zeckp n)); rewrite eq sa.
Qed.

Lemma Zeckp_prop5 n (e := Zeckp): Zeck_li n.+1 = 0 ->
  (n == 0) || 
  [&& (Zeck_li n != 0), e (e n.+1) == (e (e n)).+1 & (e (n.+1) == (e n).+1)].
Proof.
move: (Zeck_prop1 (n:=n.+1) isT) => [a [l [pa]]]. 
move: (path_all_llen pa) => ha.
have ha': all (leq 1) l by  apply/allP => [x /(allP ha)]; case x.
rewrite /Zeck_li /e /Zeckp /Zeck_valp  rev_cons => pb; rewrite pb. 
rewrite last_rcons /Zeck_val => sa sb. 
move: sa; rewrite sb !sum_rcons big_cons !add1n => /eqP. 
rewrite !eqSS => /eqP sa.
have sr: sorted ggen (rev l) by rewrite rev_sorted; exact (path_sorted pa).
have eq1 : Zeck n = rev l by rewrite sa -sum_rev; apply:ZeckP.
rewrite {1} sa eq1 eqxx sum_rev.
case rvz: (l == nil); first by rewrite (eqP rvz) big_nil.
have ->: last n (rev l) != 0.
  by move: ha rvz; case l => // b s; rewrite rev_cons last_rcons /=; case b.
rewrite andbT /=;apply/orP; right.
move: (seq_prednK ha').
set m := (\sum_(i <- l) fib i.+1); set w :=  (pred_seq l) => hb.
have sa1: sorted ggen (rev w). 
  move: sr; rewrite hb !rev_sorted sorted_llen_succ //.  
have nv: m = Zeck_val (rev w) by rewrite /m /Zeck_val hb big_map sum_rev.
have ->: Zeck m = (rev w) by rewrite nv; apply:ZeckP.
have ->: m.+1 = Zeck_val (rcons (rev w) 0) by rewrite /Zeck_val sum_rcons nv.
rewrite [X in X == _] (Zeckp_prop1) ? /Zeck_valp ? sum_rcons //.
rewrite rcons_uniq (sorted_ggen_uniq sa1) andbT; apply/negP. 
rewrite mem_rev => /mapP [x /(allP ha)]; case x => // [] [] //.  
Qed.

Lemma FR_prop1 n: Zeck_li n.+1 = 0 -> FR n.+1 = FR (Zeckp n).
Proof.
case: n; first by rewrite Zeckp_0  FR_1 FR_0.
move => n; rewrite FR_rec // => /Zeckp_prop5 /= /and3P [ea /eqP ec /eqP eb].
move:(Zeckp_prop3b ea) => ed.
by rewrite {1 3 4} eb subSS -(Zeckp_prop3b ea) -/(FR _) (FA_prop0 ec).
Qed.

Lemma FR_prop0 n: Zeck_li n != 0 ->
  FR n = FR (Zeckp n) + FA (Zeckp (Zeckp n)) (Zeckp n).-1.
Proof.
case h: (n==0); first by rewrite  (eqP  h) /Zeck_li Zeck_0.
by move =>h1;rewrite (FR_rec (negbT h)) -(Zeckp_prop3b h1).
Qed.

Lemma FR_positive n: 0 < FR n.
Proof.
elim: n {-2} n (leqnn n). 
   by move => n; rewrite leqn0 => /eqP ->; rewrite FR_0.
move => n IH n1; rewrite leq_eqVlt; case/orP=> [|Hn]; last first.
  by apply: IH; rewrite -ltnS.
move => /eqP => ->; case h:(Zeck_li n.+1 == 0).
  by move: (Zeckp_le n) => [/ IH ha hb]; rewrite (FR_prop1 (eqP h)). 
move:(FR_prop0 (negbT h)) IH; clear h; case: n; first by rewrite FR_1.
move => n -> h; move /leqifP: (Zeckp_le n.+2) => /=; rewrite ltnS => /h lt.
by apply: (leq_trans lt); rewrite leq_addr.
Qed.

Lemma FR_prop3 n: odd (Zeck_li n) -> FR n = FR (Zeckp n).
Proof.
move => h.
have H1: Zeck_li n != 0. 
  by move: h; rewrite/ Zeck_li;case : (last n (Zeck n)).
by rewrite (FR_prop0 H1) (Zeckp_prop3b H1) - (Zeckp_prop4b h) FA_prop0bis ?addn0.
Qed.

Lemma FR_prop4 m: llen 1 (Zeck_li m) ->FR (Zeckp m).+1 = FR (Zeckp (Zeckp m)).
Proof.
move => Hm;move: (Hm); rewrite /llen /ggen /= => /Zeck_li_prop2 Hm1.
rewrite /= FR_prop1 //; move: Hm Hm1; rewrite /Zeck_li; case: m => // m.
move: (Zeck_prop1 (n:=m.+1) isT) => [a [l [pa -> ->]]].
rewrite {1} rev_cons last_rcons => sc sd.
have: all (leq 1) (rev (a:: l)) by apply /allP; move => x /(allP sd)/ltnW/ltnW.
move /(seq_prednK); set s' := (pred_seq (rev (a :: l))) => sv'.
have sv:sorted ggen (rcons s' 0).
  have aa: (rev (succ_seq (rcons s' 0))) = [:: 1, a & l].
    by rewrite /succ_seq map_rcons -/(succ_seq s') - sv' - rev_cons revK.
  by rewrite -sorted_ggen_succ - rev_sorted aa /=; apply/andP.
have eq: (Zeck_valp (a :: l)).+1 = Zeck_val (rcons s' 0).
  by rewrite /Zeck_valp /Zeck_val sum_rcons - sum_rev sv' big_map.
by rewrite (Zeckp_prop1 (sorted_llen_uniq pa)) eq (ZeckP sv) last_rcons.
Qed.

Lemma FR_fib1 k: FR (fib k.*2.+3) = FR (fib k.*2.+2).
Proof.
by rewrite FR_prop3 /Zeck_li ?Zeck_fib ?Zeckp_fib //= odd_double. Qed.

Lemma FR_fib2 k: FR (fib k.*2.+1) = FR (fib k.*2).
Proof. by case k; [rewrite FR_1 FR_0 | apply: FR_fib1 ]. Qed.

Lemma FR_fib3 k: FR (fib k).-1 = 1.
Proof.
have h0:= FR_0; have h1:= FR_1.
suff H: forall k, FR (fib k.*2).-1 = 1 /\ FR (fib k.*2.+1).-1 = 1.
  move: (H k./2) => [sa sb]; rewrite - (odd_double_half k); case (odd k) => //.
clear k; case => //;elim =>  // n []; set k := n.+1 => sa sb.
set l := succ_seq  [seq i.*2 | i <- iota 0 k].
have eq1: [seq i.*2 | i <- iota 1 k] = [seq i.+1 |i <- l].
  by rewrite /l iota_S - !map_comp /comp.
have ea: Zeck (Zeck_val l) = rev l.
  rewrite -{1} (revK l) /Zeck_val sum_rev; apply: ZeckP.
  by rewrite rev_sorted /l sorted_llen_succ sorted_llen_mkseq_e.
have eb : Zeck_val l = (fib (k.+1).*2).-1.
  by rewrite - fib_sum_odd_alt  /Zeck_valp /mkseq map_cons big_cons eq1 big_map.
have res1:FR (Zeck_val l) = 1.
  have ha:odd (Zeck_li (Zeck_val l)). 
    by rewrite /Zeck_li ea /l /succ_seq -map_comp /k /= rev_cons last_rcons.
  by rewrite (FR_prop3 ha) eb Zeckp_fibc doubleS.
split; first by rewrite - eb.
set u:= [seq i.+2 | i <- l].
have ec: Zeck (Zeck_val u) = rev u.
  rewrite -{1} (revK u) /Zeck_val sum_rev /u/l - map_comp /comp - map_rev.
  apply: ZeckP. rewrite map_rev rev_sorted - map_comp  sorted_llen_mkseq //.
  by move => x; rewrite doubleS /=.
have ed: llen 1 (Zeck_li (Zeck_val u)).
   by rewrite /Zeck_li ec /u /l - !map_comp /comp /k /= rev_cons last_rcons.
have ee: Zeckp (Zeck_val u) = Zeck_val (rev ([seq i.+1 | i <- l])).
  by rewrite /Zeckp ec /Zeck_valp /Zeck_val ! sum_rev /u ! big_map.
rewrite - fib_sum_even_alt2 /mkseq map_cons eq1 /Zeck_val big_cons add1n. 
move: (FR_prop4 ed); rewrite ee /Zeck_val sum_rev - res1 => ->; congr FR.     
have uu:uniq u.
  rewrite /u /l - !map_comp /comp map_inj_uniq ?iota_uniq//.
  by move => x y /= /eqP; rewrite !eqSS eqn_double => /eqP.
have au: all (leq 1) u by apply/allP => x /mapP [y yl ->].
move: (Zeckp_prop1_bis au uu).
by rewrite /u /Zeck_val /Zeck_valp /Zeck_valpp !big_map.
Qed.

Definition Zeckpn k n:= iter k Zeckp n.

Lemma FR_split n (p := fib (Zeck_li n).+2) (m := n - p):
  n != 0 -> n = p + m /\  (m = 0 \/  llen (Zeck_li n) (Zeck_li m)).
Proof.   
rewrite /m/p; clear p m.
case:n => // n _; move: (Zeck_prop1 (n:=n.+1) isT) => [a [l [pa pb pc]]].
rewrite /Zeck_li pb rev_cons last_rcons pc Zeckv_cons addKn; split => //.
move: pa;case l; first by left;rewrite Zeckv_nil. 
move => u v /= /andP [sa sb]; right.
by rewrite /Zeck_val - sum_rev ZeckP ? rev_sorted //= rev_cons last_rcons.
Qed.


Lemma Zeckp_prop6 n m q (s := pred_seq (Zeck m)):
  n = m + fib q.+3 -> (m = 0 \/  llen q.+1 (Zeck_li m)) ->
  [/\ Zeck (Zeckp n) = rcons (Zeck (Zeckp m)) q,
     (q >0 -> Zeck (Zeckp (Zeckp n)) = rcons (Zeck (Zeckp (Zeckp m))) q.-1),
     sorted llen (q :: rev s),  Zeckp m = Zeck_val (rev s) &
    Zeckp n = fib q.+2 +  Zeckp m].
Proof.
move => sa sb; rewrite /s.
move:(Zeck_zeck_val m) (Zeck_ggen m) sb; rewrite /Zeck_li.
set l := (Zeck m) => qa qb; case => qc.
  rewrite /l sa qc /= !Zeckp_0 Zeck_0  !Zeckp_fib !Zeck_fib Zeckv_nil addn0.
  by split => // /prednK {1} <-; rewrite Zeck_fib.
have lp0: 1 < last m l by apply: (leq_trans _ qc); rewrite !ltnS leq0n.
move:(Zeck_li_prop2 (ltnW lp0)) => lp1.
have qd: sorted llen (q.+1 :: rev l).
   move: qb qc; rewrite - rev_sorted -/llen - qa - {2 3} (revK l).
   by case: (rev l) => // u v; rewrite rev_cons last_rcons /= => -> ->.
move: (seq_prednK lp1); rewrite -/s => eq1.
have qg: sorted llen (q :: rev s).
  by move:qd; rewrite /l eq1 -map_rev -map_cons -/(succ_seq _) sorted_llen_succ.
have qg':sorted ggen s by rewrite - rev_sorted; apply: (path_sorted qg).
have qe: m = Zeck_val (rev l) by rewrite - qa /Zeck_val sum_rev.
have qe': Zeck_valp s = Zeck_valp (rev s) by rewrite /Zeck_valp sum_rev.
have eq2: Zeckp m = Zeck_val (rev s).
  rewrite qe /Zeck_val !sum_rev  (Zeckp_prop0 (sorted_ggenW qb)) /l eq1.
  by rewrite /Zeck_valp big_map.
move: (Zeck_split qd (leqnn (fib q.+3))).
rewrite - qe addnC - sa Zeckp_fib => eq3.
rewrite - eq3 - eq2 qg.
have sv: Zeck (Zeckp m) = s by rewrite eq2 /Zeck_val -sum_rev ZeckP revK.
have eq4: Zeck (Zeckp n) = rcons s q.
  move: qg; rewrite - rev_sorted rev_cons revK => /ZeckP <- //.
  by rewrite eq3 /Zeck_val sum_rcons eq2 /Zeck_val sum_rev.
rewrite {3 5} /Zeckp sv eq4 qe'; split => //.
have lp2: all [pred z | 0 < z] s.
   apply /allP => [z /mapP [x /(allP (Zeck_li_prop2 lp0)) /=]].
   by case x => // m';rewrite ltnS succnK => h ->.
move: (seq_prednK lp2); set s' := [seq i.-1 | i <- s] => sv' qp.
move: qg ; rewrite - {1 2} (prednK qp) => qg.
have qg'': sorted llen (q.-1 :: rev s').
  move: qg; rewrite sv' - map_rev /llen /=.
  by elim: (rev s') (q.-1) => // u v H b /= /andP[h /H ->];rewrite -ltnS h.
have qg''':sorted ggen s' by rewrite - rev_sorted; apply: (path_sorted qg'').
rewrite/Zeck_valp sv' - map_rev big_map sum_rev  (ZeckP qg''') sum_rcons.
by rewrite big_map - (sum_rcons q.-1) ZeckP // - rev_sorted rev_rcons.
Qed.


Lemma FR_prop5 n: ~~ odd (Zeck_li n) -> (Zeck_li n) != 0 ->
  FR n =  FR (Zeckp n) + FR((Zeckp n).-1) /\ FR (Zeckp n) = FR (Zeckpn 2 n).
Proof.
pose qk n := fib (Zeck_li n).+2;pose pk n := (n - qk n).
move => ha hb.
have nz: n != 0 by apply /negP => /eqP nz; move: hb; rewrite nz /Zeck_li Zeck_0.
move: (FR_split nz); set m := _ - _; set p := fib _; move => [pb pc].
set k := (Zeck_li n)./2.-1.
have pq: (Zeck_li n) = (k.+1).*2.
  move: hb; rewrite - (odd_double_half (Zeck_li n))(negbTE ha) add0n.
  by rewrite double_eq0 -lt0n => /prednK => <-. 
move: pb; rewrite addnC /p pq doubleS => pb; rewrite pq in pc.
rewrite (FR_prop0 hb); case: pc => pc.
  by rewrite pb pc add0n {3} /FR /= !Zeckp_fib FR_fib1 -! doubleS Zeckp_fiba. 
move: (Zeckp_prop6 pb (or_intror (m = 0) pc)) => [qa _  qc qd qe].  
split.
  rewrite /FR;congr addn; congr FA.
  have: 0 < fib k.*2.+3 by rewrite fib_gt0.
  have qx := leqnn (fib (k.+1).*2.+1); have qy:= leq_pred (fib (k.+1).*2.+1).
  move/prednK => xx; rewrite qe -{2} xx addSn succnK qd.
  by rewrite (Zeck_split qc qx) (Zeck_split qc qy) Zeckp_fiba doubleS Zeckp_fib.
by apply: FR_prop3; rewrite /Zeck_li qa last_rcons /= odd_double.
Qed.

Lemma FR_fib4 k: FR (fib k.*2) = k.-1.+1.
Proof.
elim: k => [| k H]; first  by rewrite FR_0.
have h: Zeck_li (fib (k.+1).*2) = k.*2 by rewrite /Zeck_li doubleS Zeck_fib /=.
have ei: ~~ odd (Zeck_li (fib (k.+1).*2)) by rewrite h odd_double.
case kz: (k == 0); [by rewrite  (eqP kz) FR_1 | move: (negbT kz) => kp].
have mz: Zeck_li (fib (k.+1).*2) != 0 by rewrite h double_eq0 kp.
rewrite (proj1 (FR_prop5 ei mz)) doubleS Zeckp_fib FR_fib2 H FR_fib3 addn1.
by rewrite  /= prednK // lt0n.
Qed.

Theorem FR_fib k: FR (fib k) = (k./2).-1.+1.
Proof.
rewrite - {1} (odd_double_half k);case: (odd k).
  by rewrite FR_fib2 FR_fib4.
by rewrite FR_fib4.
Qed.


Lemma FR_prop6 k m: llen (k.+1).*2 (Zeck_li m) ->
   FR (fib (k.+1).*2.+1 + Zeckp m).-1 = FR (Zeckpn (k.+1).*2 m).
Proof.
rewrite (fib_pos) addSn succnK.
elim: k m => [m mv | k Hrec m mv]; first by apply:(FR_prop4 (ltnW mv)).
have ->: (Zeckpn (k.+2).*2 m) = ((Zeckpn (k.+1).*2 (Zeckp (Zeckp m)))).
  by elim k => // k1 /= ->.  
set RHS :=  RHS.
move:(Zeckp_prop6 (erefl ( m + fib (k.+1).*2.+4)) (or_intror (m = 0) mv)).
move => [_ _ pc pd _].
rewrite - fib_sum_even_alt2 /mkseq /= /Zeck_val big_cons addSn.
set l := pred_seq (Zeck m) ++ rev ([seq i.*2 | i <- iota 1 k.+1]).
set x := _ + _;  have {x} -> : x = Zeck_val l. 
   by rewrite /x/l pd /Zeck_val big_cat !sum_rev /= addnC.
set lp := succ_seq l.
have ha: sorted ggen (rcons l 0).
  have pa3 n a b: (last a [seq i.*2 | i <- iota b n.+1]) = (n + b).*2.
    by elim: n a b => // n H a b;move: (H 0 b.+1); rewrite addnS addSn.
  have pa2: sorted llen ((k.+1).*2 :: rev [seq i.-1 | i <- Zeck m]).
    by move:pc; case: (rev _) => // a s /=/andP[/ltnW /= -> ->].
  rewrite /l - rev_sorted rev_rcons rev_cat revK /= cat_path.
  move:(sorted_llen_mkseq_e 1 k.+1) => /= ->.
  by move: pa2;case k => // k'; rewrite pa3 addn2.
have hb: sorted ggen l. 
   move: ha;rewrite - rev_sorted  -(rev_sorted _ l)  rev_rcons /=. 
   by move /path_sorted.
move:(sorted_ge2_all_ps ha) => [hc hd].
move: (seq_prednK hd); set l' := (pred_seq l) => sv.
have hd' : all (leq 1) l'.
  move: hc; rewrite /l' => h; apply/allP => [x /mapP [y /(allP h) u ->]].
  by move: u; case y => //.
move: (seq_prednK hd'); set l'' := pred_seq l' => sv'.
have he: sorted ggen l' by rewrite - sorted_ggen_succ - sv.
have he': sorted ggen l'' by rewrite - sorted_ggen_succ - sv'.
have ea: Zeck_val l = Zeck_valp lp by rewrite  /Zeck_val /Zeck_valp big_map.
have eb: Zeck (Zeck_val lp) = lp by apply: ZeckP; rewrite sorted_ggen_succ.
have ec: Zeck (Zeck_val l) = l by apply: ZeckP.
have ed: Zeckp (Zeck_val lp) =  Zeck_val l by rewrite /Zeckp eb - ea.
have ee: Zeck (Zeck_val l') = l' by apply: ZeckP.
have ef: (Zeck_valp l) = Zeck_val l'. 
   by rewrite /Zeck_val /Zeck_valp sv big_map.
have eg: Zeck (Zeck_valp l) = l' by rewrite ef; apply:ZeckP.
have hf: llen 1 (Zeck_li (Zeck_val lp)).
  rewrite /Zeck_li eb /lp /l /succ_seq map_cat map_rev - ! map_comp /=.
  by rewrite last_cat rev_cons last_rcons. 
have eh: Zeck_li (Zeck_valp l) = 1.  
  rewrite /Zeck_li eg /l' /l /pred_seq map_cat map_rev - !map_comp /comp /=.
  by rewrite last_cat ! rev_cons last_rcons.
move: pc pd; set s := rev (pred_seq (Zeck m)) => pc pd.
have us:= (uniq_llen pc).
have ei: Zeckp (Zeckp m) = Zeck_valp s by rewrite pd; apply: Zeckp_prop1. 
have sb1: all (leq (k.+1).*2.+3) s.
  move: pc; elim:(s) => // a L H /=/andP [h1 h2]; rewrite h1 /=; apply:H.
  by move:h2; case:L => // a' L' /= /andP [/ltnW /(ltn_trans h1) -> ->].
have sb2: all (leq 1) s by apply/allP => [ x /(allP sb1)]; case:x.
have sb3: all (leq 2) s by apply/allP => [ x /(allP sb1)]; case:x => //; case.
move: (seq_prednK sb2); set s' :=  (pred_seq s) => s'v.
have ek: Zeck (Zeck_valp s) = rev s'.
  rewrite /Zeck_valp s'v big_map - sum_rev; apply:ZeckP.
  rewrite rev_sorted - sorted_llen_succ - s'v; exact:(path_sorted pc). 
have ej: Zeckp (Zeckp (Zeckp m)) = Zeck_valpp s. 
    by rewrite ei Zeckp_prop1_bis.
have hi:llen (k.+1).*2 (Zeck_li (Zeckp (Zeckp m))).
  move: mv sb1;rewrite /Zeck_li ei ek /s' /s -{1} (Zeck_zeck_val m).
  case: (Zeck m); first  by rewrite /= Zeckv_nil //.
  move => a l1 _; rewrite /pred_seq map_rev revK - map_comp /comp all_rev => w.
  set y := last a.-2 [seq x.-2 | x <- l1];rewrite /= -/y.
  have: y\in [seq x.-2 | x <- a::l1] by rewrite /y map_cons; apply:mem_last.
  move /mapP => [x /(map_f predn) /(allP w) xh ->]. 
  by move: xh; case x => //; case => //.
have aa:(Zeck_valp l') = Zeck_valpp l.
   by rewrite /Zeck_valp /Zeck_valpp sv /succ_seq big_map.
have: odd (Zeck_li (Zeck_valp l)) by rewrite eh.
rewrite - ed (FR_prop4 hf) ed /Zeckp ec; move /FR_prop3 => ->.
rewrite /Zeckp eg aa /Zeck_valpp /l big_cat /= - sum_rev -/s addnC sum_rev.
rewrite - map_cons -/(iota 1 k.+1) /RHS - (Hrec _ hi) ej; congr (FR (_ + _)). 
by rewrite -(fib_sum_even_alt k.+2) /Zeck_valpp /mkseq /= !big_cons /= add0n.
Qed.

Lemma FR_prop7 n (k :=Zeck_li n) (m := n -  fib (k.+2)) :
  ~~(odd k) -> FR n = FR (Zeckpn k.+1 m) + (k./2) * FR (Zeckpn k m).
Proof.
rewrite /m/k; clear.
case: n; first by rewrite /Zeck_li Zeck_0 /= sub0n Zeckp_0 addn0.
move => n sa.
set q := (Zeck_li n.+1);move: (FR_split (n:=n.+1) isT) (erefl q). 
rewrite -/q {6} /q -(odd_double_half q) (negbTE sa) add0n. 
set k := (q./2); set m := _ - _; move => [->]; case.
  have hu: forall k, Zeckpn k 0 = 0 by elim => // v /= ->; rewrite Zeckp_0.
  by move => ->; rewrite !hu FR_0 doubleK addn0 - doubleS FR_fib4 muln1 //.
move => su.
rewrite half_double; move: k m su; clear; elim.
  move => m;rewrite /= add1n addn0 => hc mz.
  set s := (succ_seq (Zeck m)); set n := Zeck_val s.
  move: (Zeck_ggen m); rewrite -sorted_ggen_succ -/s => /ZeckP ha.
  have ->: m = Zeckp n. 
    by rewrite /Zeckp ha - (Zeck_zeck_val m) /Zeck_valp /Zeck_val /s !big_map.
  have hb: Zeck_li n = (Zeck_li m).+1. 
    move: hc;rewrite /Zeck_li ha /s - {1} (Zeck_zeck_val m).
    by move: mz; case: (Zeck m) => [| u v]; rewrite ? Zeckv_nil //= last_map.
  have /FR_prop4 //: llen 1 (Zeck_li n) by rewrite hb /= ltnS hc.
move => k Hrec m sa sb.
set n := (fib (k.+1).*2.+2 + m). 
have mz: Zeck m != nil. 
  apply /eqP => s. 
  by move: (Zeck_zeck_val m) sa; rewrite /Zeck_li s Zeckv_nil => <- //.
have e1: n = m + fib (k.+1).*2.+2 by rewrite addnC.
have qa: ~~ odd (Zeck_li n) by rewrite /n sb odd_double.
have qb: Zeck_li n != 0 by rewrite /n sb double_eq0.
move: (FR_prop5 qa qb) => [qc qd]; rewrite qd in qc.
rewrite doubleS in e1.
move: (Zeckp_prop6 e1 (or_intror (m = 0) sa)) => [pa pb pc pd pe].
rewrite qc pe (FR_prop6 sa); rewrite mulSnr addnA; congr addn.
set s2:= [seq i.-2 | i <- Zeck m].
set s1:= [seq i.-1 | i <- Zeck m]; rewrite -/s1 in pc pd.
have qh : (fib k.*2.+2 + Zeckpn 2 m) = Zeckpn 2 n.
  have qh: fib (k.+1).*2.+1 <= fib k.*2.+3 by rewrite doubleS.
  by rewrite /Zeckpn /= pe pd (Zeck_split  pc qh) doubleS Zeckp_fib.
have qf:Zeck_li (fib k.*2.+2 + Zeckpn 2 m) = k.*2.
  by rewrite qh /= /Zeck_li pb // last_rcons.
move:(path_all_llen pc); rewrite all_rev => qe.
have qi: Zeck m = [seq i.+2 | i <- s2].
  move: qe;rewrite /s1/s2; elim (Zeck m) => // a l H /= /andP [ h /H <-].
  by move: h; case a => //; case.
move:(path_sorted pc); rewrite rev_sorted => /ZeckP. 
rewrite - Zeckv_rev  -pd => pf.
have pg: Zeckp (Zeckp m) = Zeck_val s2.
  by rewrite {1} /Zeckp pf /Zeck_val /Zeck_valp /s1 qi !big_map. 
have ph: Zeck (Zeckp (Zeckp m)) = s2.
   rewrite pg; apply: ZeckP; rewrite -sorted_ggen_succ -sorted_ggen_succ.
   rewrite /succ_seq - map_comp /comp - qi; apply: Zeck_ggen.
have qg: llen k.*2 (Zeck_li (Zeckpn 2 m)). 
  move: qe mz; rewrite /s1 /Zeck_li ph qi /pred_seq -map_comp /comp /=. 
  by case s2 => // a l h _ /=; move/(allP h) :(map_f succn (mem_last a l)). 
by rewrite -qh (Hrec _ qg qf)  /Zeckpn - ! iter_add // !addn2 doubleS.
Qed.


Theorem FR_prop8 n (k :=Zeck_li n) (m := n -  fib (k.+2)) :
  FR n = FR (Zeckpn k.+1 m) + (k./2) * FR (Zeckpn k m).
Proof.
case ok: (odd k); last by rewrite (FR_prop7  (negbT ok)).
move: (prednK (odd_gt0 ok)) => eq1.
have opk: ~~(odd k.-1) by move: ok;rewrite - eq1.
case nz: (n ==0); first by  move: eq1; rewrite /k (eqP nz) /Zeck_li. 
move: (Zeck_prop1 (negbT nz)) => [a [l [pa pb pc]]].
have eq2: a = k by rewrite /k /Zeck_li pb rev_cons last_rcons.
rewrite eq2 in pa pb pc.
have eq3: m = Zeck_val l by  rewrite /m pc  Zeckv_cons addKn.
have: all (leq 1) l by apply/allP => [x /(allP (path_all_llen pa))]; case x.
move/seq_prednK; set s := pred_seq l => sv.
have pd:= (path_sorted pa).
have eq4: Zeck m = rev l.
  by rewrite eq3 - Zeckv_rev; apply: ZeckP;  rewrite rev_sorted. 
have pe: (Zeck_val l) = 0 \/ llen k.-1.+1 (Zeck_li (Zeck_val l)).
  move: ok pa;rewrite /Zeck_li - eq3 eq4 {1} eq3; case l => [_ _ | x y].
     by left; rewrite Zeckv_nil.
  by rewrite rev_cons last_rcons /=; case k => // k' _ /andP [ h];right.
move: (pc); rewrite Zeckv_cons addnC - eq1 => pc'. 
move: (Zeckp_prop6 pc' pe); rewrite - eq3; move => [pf _ pg ph pi].
have eq5: (Zeck_li (fib k.-1.+2 + Zeckp m)) = k.-1. 
  by rewrite /Zeck_li -pi pf last_rcons.
have opk1: ~~odd (Zeck_li(fib k.-1.+2 + Zeckp m)) by rewrite eq5.
rewrite (FR_prop3 ok) pi (FR_prop7 opk1) eq5 addKn.
by rewrite /Zeckpn !iterSr  (evenE (negbTE opk)) doubleK /= uphalf_double.
Qed.

Lemma FR_unique n: FR n = 1 -> exists k, n = (fib k.+2).-1.
Proof.
have H k: FR k = 1 -> ((Zeck_li k)./2) = 0.
  rewrite {1} FR_prop8.
  case: (posnP (Zeck_li k)./2) => // ha.
  set u := Zeckpn _ _; set v := Zeckpn _ _ => eq1.
  have hb: 0 < (Zeck_li k)./2 * FR v by rewrite muln_gt0 ha (FR_positive v).
    by move: (leq_add  (FR_positive u) hb); rewrite eq1.
have H0: exists k, 0 = (fib k.+2).-1 by exists 0.
elim: n {-2} (n) (leqnn n); first by  move => n; rewrite leqn0 => /eqP ->.
move => b Hr n nb fz1.
case (posnP n); [by move => -> | move => np].
have H1: forall m, Zeckp m <= m.
   move => m; rewrite /Zeckp -{2} (Zeck_zeck_val m) /Zeck_val /Zeck_valp.
   elim: (Zeck m); first by rewrite !big_nil.
   move => a l HH; rewrite !big_cons leq_add // ? fib_monotone //.
have H2: forall n m, Zeckpn n m <= m.
  elim => // n1 HH m; exact (leq_trans (H1 (Zeckpn n1 m)) (HH  m)).
have n1b: n.-1 <= b by rewrite - ltnS (prednK np).
move: (H _ fz1) => fz2.
move: fz1; rewrite FR_prop8 fz2 addn0; set k := Zeck_li n.
have nnz: n != 0 by rewrite -lt0n.
move:(Zeck_prop1 nnz) => [a[l [pa pb pc]]].
have ak: a = k by rewrite /k /Zeck_li pb rev_cons last_rcons.
have: n - fib k.+2 = Zeck_val l by rewrite pc Zeckv_cons ak addKn.
have ul := (uniq_llen pa).
have lge2: all (leq a.+2) l by apply /allP => [x /(allP(path_all_llen pa))]. 
have: all (leq 1) l by apply /allP => [x /(allP lge2) ]; case: x.
move/ (seq_prednK); set s := (pred_seq l) => sv.
have ss: sorted llen s by rewrite - sorted_llen_succ - sv (path_sorted pa).
have: (k == 0) || (k == 1) by move: fz2; rewrite -/k; case k => // [] [].
case /orP => /eqP kz; rewrite kz.
  have aa: (Zeckpn 1 (n - fib 2)) <= b.
    by apply:(leq_trans (H2 1 (n - fib 2))); rewrite subn1.
  move => eqa  /(Hr _ aa) [u]; rewrite /Zeckpn /= eqa => eqb.
  have: rev (Zeck (Zeckp (Zeck_val l))) = s.
    rewrite -(revK s) (Zeckp_prop1 ul) sv /Zeck_valp big_map - sum_rev ZeckP //.
    by rewrite rev_sorted. 
  rewrite eqb -(odd_double_half u); case: (odd u). 
    rewrite add1n - doubleS Zeck_fib1 revK => h.
    have /(allP lge2) //: 1 \in l by rewrite sv (mem_map succn_inj) - h. 
  rewrite  Zeck_fib2 revK => sv2; exists ((u./2)).*2.+1.
  rewrite pc ak kz sv -sv2 /succ_seq -map_comp /comp -doubleS. 
  by rewrite -fib_sum_even_alt2  /mkseq /= iota_S - !map_comp.
have aa:  Zeckpn 2 (n - fib 3) <= b.
  apply:(leq_trans (H2 2 (n - fib 3))); rewrite subn2.
  exact(leq_trans (leq_pred n.-1) n1b).
move => eqa  /(Hr _ aa) [u]; rewrite /Zeckpn /= eqa => eqb.
have: all (leq 1) s. 
  by apply/allP => [x/mapP [y /(allP lge2) y2] ->];move: y2; case y => // [] [].
move/ (seq_prednK); set s' := pred_seq s => sv'.
have eq1 :=(Zeckp_prop1 (uniq_llen pa)).
have eq2: (Zeck (Zeckp (Zeck_val l))) = rev s.
    rewrite eq1 sv /Zeck_valp big_map - sum_rev  ZeckP //.
    by rewrite rev_sorted - sorted_llen_succ - sv (path_sorted pa).
have : rev (Zeck (Zeckp (Zeckp (Zeck_val l)))) = s'.
  rewrite -(revK s') {1}/Zeckp eq2 sv' /Zeck_valp sum_rev big_map.
  by rewrite - sum_rev ZeckP // rev_sorted - sorted_llen_succ - sv'.
rewrite eqb -(odd_double_half u); case: (odd u).
  rewrite add1n - doubleS Zeck_fib1 revK => sv2.
  have: 2 \in l by rewrite sv sv' /succ_seq -map_comp;apply/map_f; rewrite -sv2.
  by move/(allP lge2); rewrite ak kz.
rewrite  Zeck_fib2 revK => sv2; exists ((u./2).+1).*2.
rewrite pc - doubleS -fib_sum_odd_alt sv sv' - sv2 ak kz.
by rewrite /Zeck_val/Zeck_valp /mkseq/= !iota_S ! big_cons ! big_map succnK.
Qed.

Lemma Zeck_fib3 k:
   Zeck (fib (k.+2).*2).-2 = rev(0 :: mkseq (fun i=> i.*2.+3) k).
Proof.
set s := [seq i.*2.+3 | i <- iota 0 k].
rewrite - (fib_sum_odd_alt)  /Zeck_valp /mkseq /= !big_cons /=.
transitivity (Zeck (Zeck_val(0:: s))).
  by rewrite /s /Zeck_val iota_S iota_S !big_map // big_cons big_map.
rewrite - Zeckv_rev; apply: ZeckP; rewrite rev_sorted /s/=; case k => // m.
have //:(sorted llen [seq i.*2.+3 | i <- iota 0 m.+1]). 
by apply:sorted_llen_mkseq => u /=; rewrite doubleS !ltnS.
Qed.

Lemma Zeck_fib4 k:
   Zeck (fib k.*2.+3).-2 = rev (mkseq (fun i=> i.*2.+2) k).
Proof.
set s := [seq i.*2.+2 | i <- iota 0 k].
rewrite - doubleS-  (fib_sum_even_alt2 k.+1) /Zeck_val /mkseq /= big_cons /=.
rewrite iota_S - map_comp /comp /= - /(Zeck_val _) - Zeckv_rev; apply: ZeckP.
by rewrite rev_sorted; apply:sorted_llen_mkseq => u /=; rewrite !ltnS.
Qed.


Lemma FR_fib5 k: FR (fib k.*2.+4).-2 = FR(fib k.*2.+3).-2.
Proof.
rewrite - !doubleS; move: (Zeck_fib3 k).
set n := (fib (k.+2).*2).-2 => zn.
set m := Zeck_val (mkseq (fun i : nat => i.*2.+3) k).
have eq2: n = m.+1 by rewrite - (Zeck_zeck_val n) zn Zeckv_rev Zeckv_cons.
have eq1: (Zeck_li m.+1 = 0) by rewrite /Zeck_li - eq2 zn rev_cons last_rcons.
have ul: uniq (mkseq (fun i => i.*2.+3) k).
  by apply: mkseq_uniq => u v /eqP; rewrite !eqSS eqn_double => /eqP.
rewrite eq2 (FR_prop1 eq1) /m (Zeckp_prop1 ul).
rewrite - (Zeck_zeck_val ((fib (k.+1).*2.+1).-2)) (Zeck_fib4 k) Zeckv_rev.
by rewrite /Zeck_val/Zeck_valp /mkseq !big_map.
Qed.

Lemma FR_fib6 k: FR (fib (k.+2).*2.+1).-2 = (FR (fib (k.+2).*2).-2).+1.
Proof.
move: (Zeck_fib4 k.+1); rewrite /mkseq /= iota_S - map_comp /comp.
set s := [seq (x.+1).*2.+2 | x <- iota 0 k] => eq1.
set m :=  Zeck_val s.
rewrite FR_prop8; set n := (fib (k.+2).*2.+1).-2.
rewrite /Zeck_li eq1 rev_cons last_rcons /= mul1n.
have ->: (n - fib 0.*2.+4) = m.
  by rewrite - (Zeck_zeck_val n) /n eq1 Zeckv_rev Zeckv_cons addKn.
set s1 := [seq (x.+1).*2.+1 | x <- iota 0 k].
set s2 := [seq (x.+1).*2 | x <- iota 0 k].
have eq2 : s = [seq i.+1 | i <- s1] by rewrite /s /s1 - map_comp.
have eq3 : s1 = [seq i.+1 | i <- s2] by rewrite /s1 /s2 - map_comp.
have ha: sorted llen s2 by apply:sorted_llen_mkseq => u /=; rewrite !ltnS.
have hb: sorted llen s1 by rewrite eq3 sorted_llen_succ.
have hc: sorted llen s by rewrite eq2 sorted_llen_succ.
have eq4: Zeck m = rev s. 
   by rewrite /m - Zeckv_rev; apply: ZeckP; rewrite rev_sorted.
have eq5: Zeckp m = Zeck_val s1.
  by rewrite /Zeckp eq4 /Zeck_val /Zeck_valp sum_rev eq2 big_map.
have eq6: Zeck (Zeckp m) = rev s1.
  by rewrite eq5 - Zeckv_rev; apply: ZeckP; rewrite rev_sorted.
have eq7: Zeckp (Zeckp m) = Zeck_val s2.
  by rewrite /Zeckp eq6 /Zeck_val /Zeck_valp sum_rev eq3 big_map.
have eq8: Zeck (Zeckp (Zeckp m)) = rev s2.
  by rewrite eq7 - Zeckv_rev; apply: ZeckP; rewrite rev_sorted.
have eq9: (Zeck_valp (rev s2)) = (fib (k.+1).*2).-1.
  rewrite  Zeckvp_rev - fib_sum_odd_alt /mkseq /= /s2 Zeckvp_cons /=.
  rewrite iota_S - map_comp //.
have eq10 :(Zeck_val s2) = (fib k.*2.+3).-2.
   by rewrite - Zeckv_rev - (Zeck_fib4 k) Zeck_zeck_val.
by rewrite {1} /Zeckp eq8 eq7 eq9 FR_fib3 eq10 -FR_fib5.
Qed.

Theorem FR_fib7 k:  FR (fib k.+3).-2 = (k.+2)./2.
Proof.
have H: forall u, FR (fib u.*2.+3).-2 = u.+1.
  elim; first by rewrite FR_0.
  by move => n Hr; rewrite - doubleS FR_fib6 // ! doubleS FR_fib5 Hr.
rewrite -(odd_double_half k); case: (odd k).
  by rewrite  FR_fib5 H /= uphalf_double.
by rewrite H /= doubleK.
Qed.

Lemma FR_fib_sum1 i k: 2 <= k -> 
  FR(fib (i+ k.+2) + fib k) = (i.+3)./2 + (k./2).-1 * (i.+4)./2.
Proof.
move => kp.
have eq1: k = k.-2.+2 by move: kp; case:k => // [] [].
set l := [:: k+i ; k.-2].
have sl: sorted ggen l by rewrite /= - eq1 leq_addr.
move: (ZeckP sl); rewrite {1}/l /Zeck_val !big_cons big_nil - eq1 addn0.
rewrite (addnC k) - ! addnS;  set n:= (fib (i+ k.+2) + fib k) => eq2.
rewrite FR_prop8 /Zeck_li eq2 /l /= - eq1 /n addnK.
have ->: (Zeckpn k.-2 (fib (i + k.+2))) = fib (i + 4).
  rewrite {2} eq1 -!addSnnS addn0 addnC; elim: (k.-2) (i.+3) => // h H /= j.
  by rewrite  addSnnS H Zeckp_fib.
by rewrite addn4 Zeckp_fib !FR_fib {2} eq1.
Qed.

Lemma FR_fib_sum2 i j k : 2 <= k -> k.+2 <= j -> j.+2 <= i ->
  FR(fib i + fib j + fib k) = (i-j+1)./2 + ((j-k-1)./2) * (i-j+2)./2
    + (k./2.-1)*( (i-j+1)./2 + (j-k)./2 * (i-j+2)./2).
Proof.
move => ha hb hc.
have eq1: k = k.-2.+2 by move: ha; case k => // [] [].
have eq2: j = j.-2.+2 by move: hb; case j => // [] [].
have eq3: i = i.-2.+2 by move: hc; case i => // [] [].
set l := [:: i.-2; j.-2 ; k.-2].
have sl: sorted ggen l.
  rewrite /= - eq1 - eq2 - (ltnS j) - (ltnS j.+1) - eq3 hc.
  by rewrite  - (ltnS k) - (ltnS k.+1) - eq2 hb.
move: (ZeckP sl); rewrite {1}/l /Zeck_val !big_cons big_nil -eq1 -eq2 -eq3. 
rewrite addn0 addnA; set n := (fib i + fib j + fib k) => eq4.
have eq5: (n - fib k) = fib i + fib j by rewrite /n addnK.
rewrite FR_prop8 /Zeck_li eq4 /l /= - eq1 eq5 {5} eq1.
rewrite -(subnK hc); set i1 := i - j.+2. 
rewrite -(subnK hb); set j1 := j - k.+2.
rewrite - addSnnS  - addSnnS - addSnnS - addSnnS !addnK !addn1 addnA.
pose A n := (fib (i1.+2 + j1.+2 + n) + fib (j1.+2 + n)).
have Av m: A m = (fib (i1 + (j1.+2 + m).+2) + fib (j1.+2 + m)).
  by rewrite /A - addnA addSnnS addSnnS.
have zl m:  Zeck_val [:: (i1.+2 + j1 + m);  (j1 + m) ] = A m.
     by rewrite /Zeck_val  !big_cons big_nil addn0 /A !addnS ! addSn.
have zl' m:  Zeck_valp [:: (i1.+2 + j1 + m.+1);  (j1 + m.+1) ] = A m.
     by rewrite /Zeck_valp  !big_cons big_nil addn0 /A !addnS ! addSn.
have aux: forall n, Zeckp (A n.+1) = A n.
   move => m. rewrite - zl Zeckp_prop1 // /= mem_seq1 andbT -addnA.
   by rewrite - {2} (add0n (j1 + m.+1)) eqn_add2r.
have aux2 a b: (Zeckpn a (A (a+b))) = A b.
   by elim: a b => // a H b /=; rewrite addSnnS H aux.
rewrite -/(A _) {2 5} eq1 - addn2 aux2 aux Av Av addn1 FR_fib_sum1 // !addn2. 
rewrite FR_fib_sum1 // subn1 //. 
Qed.

Lemma FR_fib_sum3 i j : 4 <= j -> j.+2 <= i ->
  FR(fib i + fib j + 1) = (i-j+1)./2 + (j-3)./2 * (i-j+2)./2.
Proof.
by move => ha hb; rewrite (FR_fib_sum2 (leqnn 2) ha hb) mul0n addn0 - subnDA.
Qed.

Lemma FR_fib_sum4 i j : 5 <= j -> j.+2 <= i ->
  FR(fib i + fib j + 2) = (i-j+1)./2 + (j-4)./2 * (i-j+2)./2.
Proof.
move => ha hb; have hc:=(subnK (ltn_trans (leqnn 4) ha)).
by rewrite (FR_fib_sum2 (leqnSn 2) ha hb) mul0n -subnDA addn0.
Qed.

Lemma FR_fib_sum5 i: FR(fib (i + 4) + 1) = (i.+3)./2.
Proof. by rewrite (FR_fib_sum1 i (leqnn 2)) mul0n addn0. Qed.

Lemma FR_fib_sum6 i: FR(fib (i + 5) + 2) = (i.+3)./2.
Proof. by rewrite (FR_fib_sum1 i (leqnSn 2)) addn0. Qed.

Lemma FR_fib_sum7 i: FR(fib (i + 6) + 3) = (i.+3)./2 + (i.+4)./2.
Proof. by rewrite (FR_fib_sum1 i) //= mul1n. Qed.

Lemma FR_fib_sum8 i: FR(fib (i + 6) + 4) = (i.+3)./2.
Proof.
have ha : 5 <i +6 by apply (leq_trans (leqnn 6)); apply: leq_addl.
move: (FR_fib_sum3 (leqnn 4) ha); rewrite - addnA  => ->.
by rewrite addn0 (addnA i 2 4) addnK addn2 addn1 /=.
Qed.

Lemma fib_times2 i: (fib i.+2) * 2 = fib i.+3 + fib i.
Proof.
by rewrite  muln2 - addnn {1} fibSS addnAC (addnC (fib i.+1)) - fibSS.
Qed.

Lemma fib_times3 i: (fib i.+2) * 3 = fib i.+4 + fib i.
Proof.
rewrite (fibSS i.+2) addnAC (fibSS i.+1). 
by rewrite addnC -addnA -fibSS addnn -muln2 -mulnS.
Qed.

Lemma fib_times4 i: (fib i.+2) * 4 = fib i.+4 + fib i.+2 + fib i.
Proof.
rewrite (fibSS i.+2) - addnA - addnA (addnA (fib i.+2)) addnn.
by rewrite (fibSS i.+1) addnACA - fibSS - muln2 - mulnS - mulnSr.
Qed.

Lemma FR_fib_sum9 i: FR ((fib i.+4) * 2) = ((i./2)*2).+2.
Proof. by rewrite fib_times2 (_: i.+1.+4 = 1 + i.+4) // FR_fib_sum1. Qed.

Lemma FR_fib_sum10 i: FR ((fib i.+4) * 3) = ((i./2)*3).+2.
Proof. by rewrite fib_times3 (_: i.+2.+4 = 2 + i.+4) // FR_fib_sum1. Qed.

Lemma FR_fib_sum11 i: FR ((fib i.+4) * 4) = ((i./2)*3).+1.
Proof.
by rewrite fib_times4 (FR_fib_sum2) // - add2n - (add2n i.+2) !addnK.
Qed.

Lemma FR_lucas1 n: FR (lucas n.+3) = n./2.*2.+1.
Proof.
have h: 1 < n +2 by rewrite addn2 !ltnS.
by move: (FR_fib_sum1 0 h); rewrite addn2 lucas_fib // muln2 //.  
Qed.

Lemma FR_lucas2 n: FR (lucas n.*2.+3) = n.*2.+1.
Proof. by rewrite FR_lucas1 doubleK. Qed.

Lemma FR_lucas3 n: FR (lucas n.*2.+4) = n.*2.+1.
Proof. by rewrite FR_lucas1 /= uphalf_double. Qed.


Lemma FR_lucas4 k j: j.*2.+2 <= k -> 1 <= j ->
 FR (lucas (j.*2) * (fib k)) = j.*2 + (j.*2.+1)*(k./2-j-1).
Proof.
move => h h1.
rewrite (fib_lucas1 (ltnW(ltnW h))) odd_double.
have lt1: 1 < k - j.*2 by rewrite -(subnK h) -(add2n j.*2) addnA addnK addn2.
have lt2: j.*2 <= k by apply: leq_trans h; rewrite - addn2 leq_addr.
have eb: (j * 4).-2.+2 = j.*2.*2.
    by rewrite - (prednK h1) mulSnr addn4 /= -addn4 -mulSnr -!muln2 -mulnA.
have ea:(k + j.*2) = (j*4).-2 + (k - j.*2).+2. 
  rewrite - addSnnS - addSnnS eb - (addnn j.*2) - addnA subnKC // addnC//.
rewrite ea (FR_fib_sum1 _ lt1) eb /= doubleK uphalf_double mulnC. 
by rewrite -{2}(subnK lt2) halfD odd_double doubleK andbF add0n addnK subn1.
Qed.


