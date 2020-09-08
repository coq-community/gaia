(** * Theory of Sets : Ordinals
  Copyright INRIA (2017) Marelle Team (Jose Grimm).
*)

(* $Id: sset16a.v,v 1.2 2018/07/13 05:59:59 grimm Exp $ *)

Require Import BinNat.

Set Warnings "-notation-overridden".
From mathcomp
Require Import     ssreflect ssrfun ssrbool eqtype  ssrnat div.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

(* The objective of this file is to provide an explicit form for
  a function defined by a complicated form. 
  We have two variants; as a binary number or as a natural number
  Computation is  binary, reasoning is nat.
*)
Module Nds.

(* Ancillary lemmas that sow equivalence of unary/ninary numbers *)
  
Lemma NoB_add a b : N.add(bin_of_nat a) (bin_of_nat b) = bin_of_nat (a +b).
Proof.
by rewrite - (nat_of_binK (_ + _)%num) nat_of_add_bin !bin_of_natK. 
Qed.


Lemma NoB_mul a b : N.mul (bin_of_nat a) (bin_of_nat b) = bin_of_nat (a  * b).
Proof.
by rewrite - (nat_of_binK (_ * _)%num) nat_of_mul_bin !bin_of_natK. 
Qed.


Lemma NoB_ler a b: N.le (bin_of_nat a) (bin_of_nat b) -> a <= b.
Proof.
move => h; case: (leqP a b) => // lba; case /N.nlt_ge:h.
by rewrite - (subnKC lba) addSnnS - NoB_add; apply:N.lt_add_pos_r.
Qed.

Lemma NoB_ltr a b:  N.lt(bin_of_nat a) (bin_of_nat b) -> a < b.
Proof.
move => /N.nle_gt h; case: (leqP b a) => // lba; case:h.
by rewrite - (subnKC lba) - NoB_add; apply: N.le_add_r. 
Qed.


Definition ndsCb n := (n * (2 ^ (n.-1))) .+1.
Definition ndsC  := locked  ndsCb.

Lemma ndsCE n : ndsC n = ndsCb n.
Proof. by rewrite /ndsC - lock. Qed.

Lemma ndsC0 : ndsC 0 =  1.
Proof. by rewrite ndsCE. Qed.


Definition nds_k_of n :=
  if (n <=8) then n.-1 else if (n== 9) then 4 else if (n== 13) then 6 else
  if (n==19) then 6 else 5.

Definition nds_value n c := let k := n %/5 in let i := n %% 5 in 
      if n <= 7 then c n else
       if (i== 0)  then (c 5) ^ k
       else if (i==1) then (c 6) * (c 5) ^ k.-1
       else if (i==2) then (c 6) ^ 2  * (c 5) ^ k.-2
       else if (i==3) then
         if(k== 1) then  (c 4) ^ 2 else if(k==2) then (c 4) ^ 2 * (c 5)
         else (c 6)^3  * (c 5) ^ (k-3)
       else (c 4)  * (c 5) ^ k.

Definition nds_sol n := if n is m.+1 then nds_value m ndsC else 1.

Lemma nds_sol0: nds_sol 0 = 1. Proof. by []. Qed.
Lemma nds_sol1: nds_sol 1 = 1.
Proof. by rewrite /nds_sol/nds_value /= ndsC0. Qed.


Lemma nds_k_of_bd n: 1 <n -> 0 < nds_k_of n < n.
Proof.
rewrite /nds_k_of.
case: (ltnP 8 n); last by case: n => //; case => // n /=; rewrite ltnS.
case: eqP; [by move -> |  case: eqP ; [ by move -> | ]].
by case: eqP; [by move -> | move => _ _ _ /= n8 _]; apply: leq_trans n8. 
Qed.

Lemma nds_sol_with_k n: 1 < n ->
  nds_sol n = (ndsC (nds_k_of n)) * nds_sol (n - (nds_k_of n)).
Proof.
move => l1n.
move: (ltn_predK l1n) => np.
have -> : (n - (nds_k_of n)) = (n.-1 - (nds_k_of n)).+1.
  move:(nds_k_of_bd l1n) =>/andP[_]; rewrite - {2 3} np ltnS => eqa.
  by rewrite - (subSn eqa).
rewrite - {1} np /nds_k_of /nds_sol /nds_value.
rewrite - ltnS np.
case: (ltnP 8 n); last by rewrite subnn /= ndsC0 muln1.
case n9: (n == 9) => en8.
  have ->: (n.-1 - 4)  = 4  by rewrite (eqP n9).
  have ->: n.-1 %% 5 = 3 by rewrite (eqP n9).
  have ->: n.-1 %/ 5 == 1 by rewrite (eqP n9).
  by rewrite /= mulnn.
case n13: (n == 13).
  have ->: (n.-1 - 6)  = 6  by rewrite (eqP n13).
  have ->: n.-1 %% 5 = 2 by rewrite (eqP n13).
  have ->: (n.-1 %/ 5).-2 = 0 by rewrite (eqP n13).
  by rewrite /= expn0 muln1 mulnn.
case n19: (n == 19).
  have ->: (n.-1 - 6)  = 12  by rewrite (eqP n19).
  have ->: n.-1 %% 5 = 3 by rewrite (eqP n19).
  have ->: n.-1 %/ 5 = 3 by rewrite (eqP n19).
  by rewrite /= subnn expn0 mulnA - expnS.
set m := n.-1 - 5.
have mv : n.-1 = m + 5.
  rewrite /m  subnK // - ltnS np; exact (leq_trans (isT: 6 <= 9) en8).
have l4m: 4 <= m.
  by rewrite - (leq_add2r 5) - mv - ltnS np ltn_neqAle en8 andbT eq_sym n9.
rewrite mv modnDr.
case: (ltnP 7 m); last first.
   rewrite leq_eqVlt ltnS leq_eqVlt ltnS leq_eqVlt; case/or4P.
  + move  => lt1.
    suff w: (n == 13) by  move: n13; rewrite w.
    by rewrite -  np mv (eqP lt1). 
  + by move/eqP ->; rewrite /= expn1 mulnC.
  + by move/eqP ->; rewrite /= mulnn.
  + move => lt1.
    have: m == 4 by rewrite eqn_leq - ltnS lt1 l4m.
    by move/eqP ->; rewrite /= expn1 mulnC.
move: (@divnMDl 1 m 5 isT); rewrite mul1n addnC add1n => ->.
move => lm7.
move: (divn_eq m 5) => qr.
move: (ltn_pmod m (isT: 0 < 5)) => lr5.
have qp: (0 < m %/ 5).
  move: (leq_trans (isT: 5 <= 8) lm7).
  by rewrite {1} qr; case (m %/ 5) => //; rewrite add0n leqNgt lr5. 
case: ifP; first by rewrite - expnS.
case: ifP; first  by rewrite mulnCA - expnS (prednK qp).
case: ifP.
  move => r2; rewrite /= mulnCA - expnS.
  have hu: 2 <= (m %/ 5).
    rewrite ltn_neqAle qp andbT.
    apply/negP => /eqP q1;  suff w: (n == 13) by  move: n13; rewrite w.
    by rewrite - np mv qr - q1 (eqP r2).
  by rewrite - {1} (subnK hu) subn2 addn2.
case: ifP; last by rewrite  mulnCA - expnS.
rewrite eqSS eqSS; move: (ltn_eqF qp); rewrite eq_sym => ->.
case q5: (m %/ 5 == 1); first by rewrite mulnC.
case q7: (m %/ 5 == 2) => r3 _ _ _.
  suff w: (n == 19) by  move: n19; rewrite w.
  by rewrite - np mv qr (eqP r3) (eqP q7). 
rewrite mulnCA - expnS; congr (_ * _ ^ _).
move: qp q5 q7; case: ((m %/ 5)) => //; case => //; case => // q _ _ _.
by rewrite - addn3 addnK - addn3 addnK.
Qed.

Lemma nds_value_prop f: 
  f 0 = 1 -> f 1 = 1 ->
  (forall n, 1 < n ->  f n = (ndsC (nds_k_of n)) * f (n - (nds_k_of n))) ->
  (forall n,  f n = nds_sol n).
Proof.
move => H0 H1 Hr.
move => n; move: (leqnn n); elim: n {- 2} (n).
  by move => n; rewrite leqn0 => /eqP ->; rewrite H0 nds_sol0.
move => n Hrec p; rewrite leq_eqVlt; case/orP; last by rewrite ltnS => /Hrec.
move/eqP ->.
case: (posnP n) => np; first by rewrite np H1  nds_sol1.
have ng1: 1 < n.+1 by rewrite ltnS.
move: (nds_k_of_bd ng1) => /andP[kp]; rewrite ltnS => cp1.
move: kp; rewrite -(ltn_add2r (n - nds_k_of n.+1)) add0n (subnKC cp1) => lt2.
by rewrite (Hr _ ng1) (nds_sol_with_k ng1) Hrec // (subSn cp1).
Qed.


                                                     
Lemma nds_sol_max n: 1 < n ->
  exists2 k, 0 < k < n & (nds_sol n = (ndsC k) * (nds_sol (n - k))).
Proof.
move=> np.
move:   (nds_k_of_bd np)  (nds_sol_with_k  np) => ha hb.
by exists (nds_k_of n). 
Qed.

Lemma nds_sol_rec5 n: 15 <= n -> nds_sol (n + 5) = ndsC 5 * nds_sol n.
Proof.
move => ha.
have lt1: 1 < n +5 by  rewrite addnC.
by rewrite (nds_sol_with_k lt1) addnC -(subnKC ha) addnA. 
Qed.


Lemma nds_soll7 n: n <= 7 -> nds_sol n.+1 = ndsC n.
Proof. by  rewrite /nds_sol/nds_value => ->.  Qed.

Lemma nds_sol2: nds_sol 2 = ndsC 1.  Proof. by apply: nds_soll7. Qed.
Lemma nds_sol3: nds_sol 3 = ndsC 2.  Proof. by apply: nds_soll7. Qed.
Lemma nds_sol4: nds_sol 4 = ndsC 3.  Proof. by apply: nds_soll7. Qed.
Lemma nds_sol5: nds_sol 5 = ndsC 4.  Proof. by apply: nds_soll7. Qed.
Lemma nds_sol6: nds_sol 6 = ndsC 5.  Proof. by apply: nds_soll7. Qed.
Lemma nds_sol7: nds_sol 7 = ndsC 6.  Proof. by apply: nds_soll7. Qed.
Lemma nds_sol8: nds_sol 8 = ndsC 7.  Proof. by apply: nds_soll7. Qed.
Lemma nds_sol9: nds_sol 9 = ndsC 4 ^2.  Proof. by []. Qed.
Lemma nds_sol10: nds_sol 10 = ndsC 4 * ndsC 5.  Proof. by []. Qed.
Lemma nds_sol11: nds_sol 11 = ndsC 5 ^2. Proof. by []. Qed.
Lemma nds_sol12: nds_sol 12 = ndsC 5 * ndsC 6. Proof. by rewrite mulnC . Qed.
Lemma nds_sol13: nds_sol 13 = ndsC 6 ^2.
Proof. by rewrite /nds_sol /nds_value /= expn0 muln1. Qed.
Lemma nds_sol14: nds_sol 14 = ndsC 4 ^2  * ndsC 5.  Proof. by []. Qed.
Lemma nds_sol15: nds_sol 15 = ndsC 4 * ndsC 5 ^2.  Proof. by []. Qed.
Lemma nds_sol16: nds_sol 16 = ndsC 5 ^3.  Proof. by []. Qed.
Lemma nds_sol17: nds_sol 17 = ndsC 5 ^2  * ndsC 6.
Proof.  by rewrite mulnC. Qed.
Lemma nds_sol18: nds_sol 18 = ndsC 5 * ndsC 6 ^ 2.
Proof. by rewrite /nds_sol /nds_value /= mulnC expn1. Qed.
Lemma nds_sol19: nds_sol 19 = ndsC 6 ^ 3.
Proof. by rewrite /nds_sol /nds_value /= expn0 muln1. Qed.
Lemma nds_sol20: nds_sol 20 =  ndsC 4 * ndsC 5 ^3. Proof.  by []. Qed.
Lemma nds_sol21: nds_sol 21 =  ndsC 5 ^4.  Proof.  by []. Qed.
Lemma nds_sol22: nds_sol 22 =  ndsC 5 ^3 * ndsC 6.
Proof.  by  rewrite mulnC. Qed.
Lemma nds_sol23: nds_sol 23 =  ndsC 5 ^2 * ndsC 6 ^ 2.
Proof.  by  rewrite mulnC. Qed.
Lemma nds_sol24: nds_sol 24 =  ndsC 5 * ndsC 6 ^ 3.
Proof. by rewrite /nds_sol /nds_value /= mulnC expn1. Qed.
Lemma nds_sol25: nds_sol 25 =  ndsC 4 * ndsC 5 ^ 4.   Proof.  by []. Qed.
Lemma nds_sol26: nds_sol 26 =  ndsC 5 ^ 5.   Proof.  by []. Qed.


Lemma nds_sol_aux k n:
   k <= 7 -> 0 < n < 20 -> ndsC k * nds_sol n <= nds_sol (n + k).
Proof.
have M m n1 n2 : (n1 <= n2) -> (n1 * m <= n2 * m).
   by move => h; rewrite leq_mul2r h orbT.
have Hq q: 0 < q ->  ndsC 1 * ndsC q <= ndsC q.+1.
  move => qp; apply: ltnW.
  rewrite !ndsCE -[ndsCb 1] /(2) (* bug *) /ndsCb  mul2n doubleS ltnS -mul2n mulnCA - expnS.
  rewrite /= (prednK qp) mulSn - add1n -addSnnS leq_add2r.
  by rewrite -{1} [2]/(2^1) leq_exp2l.
move => ha /andP [np hb]; move: ha hb.
move => k7.
have Hp:  n < 2 ->  ndsC k * nds_sol n <= nds_sol (n + k).
  move => n2.
  have : n == 1 by rewrite eqn_leq - ltnS n2 np.
  by move => /eqP ->; rewrite add1n nds_sol1  muln1 /nds_sol /nds_value k7.
move => n20.
have cv1: bin_of_nat (ndsC 1) = 2%num by rewrite  ndsCE.
have cv2: bin_of_nat (ndsC 2) = 5%num by rewrite  ndsCE.
have cv3: bin_of_nat (ndsC 3) = 13%num by rewrite  ndsCE.
have cv4: bin_of_nat (ndsC 4) = 33%num by rewrite  ndsCE.
have cv5: bin_of_nat (ndsC 5) = 81%num by rewrite  ndsCE.
have cv6: bin_of_nat (ndsC 6) = 193%num by rewrite  ndsCE.
have cv7: bin_of_nat (ndsC 7) = 449%num by rewrite ndsCE.

have H a b: (bin_of_nat a < bin_of_nat b)%num -> a <= b by move/NoB_ltr /ltnW.
have c6666_45555 : ndsC 6 * ndsC 6 * ndsC 6 * ndsC 6 <=
                   ndsC 4 * ndsC 5 * ndsC 5 * ndsC 5 * ndsC 5.
  by apply: H; rewrite - 7! NoB_mul cv4 cv5 cv6.
have c4455_666 : ndsC 4 * ndsC 4 * ndsC 5 * ndsC 5 <= ndsC 6 * ndsC 6 * ndsC 6.
  by apply: H; rewrite - 5! NoB_mul cv4 cv5 cv6.
have c444_66 : ndsC 4 * ndsC 4 * ndsC 4 <= ndsC 6 * ndsC 6.
  by apply: H; rewrite - 3! NoB_mul cv4 cv6.
have c77_455 : ndsC 7 * ndsC 7 <= ndsC 4 * ndsC 5 * ndsC 5.
   by apply: H; rewrite - 3! NoB_mul cv7 cv4 cv5.
have c67_445 : ndsC 6 * ndsC 7 <= ndsC 4 * ndsC 4 * ndsC 5.
   by apply: H; rewrite - 3! NoB_mul cv6 cv7 cv4 cv5.
have c57_66 : ndsC 5 * ndsC 7 <= ndsC 6 * ndsC 6.
   by apply: H; rewrite - 2! NoB_mul cv6 cv7 cv5.
have c47_56 : ndsC 4 * ndsC 7 <= ndsC 5 * ndsC 6.
   by apply: H; rewrite - 2! NoB_mul cv6 cv7 cv5 cv4.
have c37_55 : ndsC 3 * ndsC 7 <= ndsC 5 * ndsC 5.
   by apply: H; rewrite - 2! NoB_mul cv3 cv7 cv5.
have c27_45 : ndsC 2 * ndsC 7 <= ndsC 4 * ndsC 5.
   by apply: H; rewrite - 2! NoB_mul cv2 cv7 cv5 cv4.
have c26_35 : ndsC 2 * ndsC 6 <= ndsC 3 * ndsC 5.
   by apply: H; rewrite - 2! NoB_mul cv6 cv2 cv3 cv5.
have c25_34 : ndsC 2 * ndsC 5 <= ndsC 3 * ndsC 4.
   by apply: H; rewrite - 2! NoB_mul cv2 cv3 cv4 cv5.
have c24_33 : ndsC 2 * ndsC 4 <= ndsC 3 * ndsC 3.
   by apply: H; rewrite - 2! NoB_mul cv2 cv3 cv4.
have c36_45 : ndsC 3 * ndsC 6 <= ndsC 4 * ndsC 5.
   by apply: H; rewrite - 2! NoB_mul cv3 cv4 cv5 cv6.
have c35_44 : ndsC 3 * ndsC 5 <= ndsC 4 * ndsC 4.
   by apply: H; rewrite - 2! NoB_mul cv3 cv4 cv5.
have c46_55 : ndsC 4 * ndsC 6 <= ndsC 5 * ndsC 5.
   by apply: H; rewrite - 2! NoB_mul cv6 cv4 cv5.
have c23_6 : ndsC 2 * ndsC 3 <= ndsC 5.
   by apply: H; rewrite - NoB_mul cv2 cv3 cv5.
have c22_4 : ndsC 2 * ndsC 2 <= ndsC 4.
   by apply: H; rewrite - ! NoB_mul cv2 cv4.
have c34_7 : ndsC 3 * ndsC 4 <= ndsC 7.
   by apply: H; rewrite - NoB_mul cv4 cv3 cv7.
have c33_6 : ndsC 3 * ndsC 3 <= ndsC 6.
   by apply: H; rewrite - ! NoB_mul cv3 cv6.
have c24_6 := (leq_trans c24_33 c33_6).
have c255_62: ndsC 2 * ndsC 5 * ndsC 5 <= ndsC 6 ^ 2.
  apply: (leq_trans (M (ndsC 5) _ _ c25_34)).
  by rewrite mulnAC - mulnn; apply: (leq_trans (M (ndsC 4) _ _  c35_44)).
have c26_44:= (leq_trans c26_35 c35_44).
have c17_44:  ndsC 1 * ndsC 7 <= ndsC 4 ^ 2
  by apply: H; rewrite - mulnn - 2! NoB_mul cv1 cv4 cv7.
have c25_7:= (leq_trans c25_34 c34_7). 
have c366_555: (ndsC 3 * ndsC 6 * ndsC 6 <= (ndsC 5) ^3).
  apply: (leq_trans(M (ndsC 6) _ _ c36_45)).
  by rewrite mulnAC expnSr - mulnn; apply: M.
have c344_56: ndsC 3 * ndsC 4 * ndsC 4 <= ndsC 5 * ndsC 6.
  by apply: (leq_trans(M (ndsC 4) _ _ c34_7)); rewrite mulnC.
have c345_66: ndsC 3 * ndsC 4 * ndsC 5 <= ndsC 6 * ndsC 6.
  by apply: (leq_trans(M (ndsC 5) _ _ c34_7)); rewrite mulnC.
have c_456_555:  ndsC 4 * ndsC 5 * ndsC 6 <= ndsC 5 ^ 3.
  by rewrite mulnAC expnS - mulnn mulnA; apply:M.
have E4: (ndsC 4) ^5 <= (ndsC 5) ^4.
  rewrite 3! expnS 2!mulnA; apply: (leq_trans (M ((ndsC 4) ^2) _ _ c444_66)).
  by rewrite - mulnn mulnACA mulnC  mulnn  -{4}[4]/(2 * 2) expnM leq_sqr - mulnn.
  
have E5: (ndsC 6) ^5 <= (ndsC 5) ^6.
  rewrite 3!expnSr - mulnn; apply: (leq_trans (M (ndsC 6) _ _ c6666_45555)).
  rewrite - (mulnA (ndsC 4))  mulnn - (mulnA (ndsC 4)) - expnSr.
  rewrite  - (mulnA (ndsC 4)) - expnSr mulnAC (expnS _ 5) (expnS _ 4) mulnA.
  by apply: M.
  
move: k7 n20.
rewrite leq_eqVlt; case/orP => k7.
  rewrite  (eqnP k7) ltnS leq_eqVlt; case/orP => n19.
    rewrite (eqnP n19) nds_sol19 nds_sol26.
    rewrite mulnC expnSr - mulnA mulnC.
    apply: (leq_trans (M (ndsC 6 ^2) _ _ c67_445)).
    rewrite mulnn mulnAC -expnMn  (expnSr _ 4); apply: M.
    by rewrite -{4}[4]/(2 * 2) expnM leq_sqr - mulnn.
   move: n19; rewrite ltnS leq_eqVlt; case/orP => n18.
     rewrite (eqnP n18) nds_sol18 nds_sol25 mulnA mulnAC - mulnn mulnA.
     rewrite expnSr mulnA (mulnC (ndsC 7)); apply: (M). 
     apply:(leq_trans (M (ndsC 6) _ _ c67_445)).
     rewrite expnS mulnA (mulnC _ (_ ^2)) - mulnn (mulnAC (ndsC 4)) - mulnA.
     by rewrite mulnC; apply M.
   move: n18; rewrite ltnS leq_eqVlt; case/orP => n17.
     rewrite  (eqP n17) nds_sol17 nds_sol24 - mulnn - mulnA mulnCA mulnA.
     by rewrite expnS  (mulnA (ndsC 5)) (mulnC _ (_ ^2)); apply: M.
   move: n17; rewrite ltnS leq_eqVlt; case/orP => n16.
     rewrite  (eqP n16) nds_sol16 nds_sol23 expnS mulnA (mulnC (ndsC 7)).
     by rewrite (mulnC (_ ^2)) - (mulnn (ndsC 6)); apply: M.
   move: n16; rewrite ltnS leq_eqVlt; case/orP => n15. 
     rewrite (eqP n15) nds_sol15 nds_sol22 mulnA (expnSr _ 2).
     by rewrite (mulnC (ndsC 7)) -(mulnA (_ ^2))(mulnC ((ndsC 5)^2)); apply: M.
   move: n15; rewrite ltnS leq_eqVlt; case/orP => n14.
     rewrite (eqP n14) nds_sol14 nds_sol21  mulnA (expnSr _ 3); apply: (M).
     rewrite -mulnn mulnA (mulnC (ndsC 7)).
     by apply: (leq_trans (M (ndsC 4) _ _ c47_56)); rewrite  mulnC mulnA. 
   move: n14; rewrite ltnS leq_eqVlt; case/orP => n13.
     rewrite (eqP n13) nds_sol13 nds_sol20 - mulnn mulnCA mulnA.
     apply: (leq_trans (M (ndsC 6) _ _ c67_445)).
     rewrite -mulnA mulnACA (mulnC _ (ndsC 6)) (mulnC _ (_ ^3)) mulnA.
     by apply:M.
   move: n13; rewrite ltnS leq_eqVlt; case/orP => n12.
     rewrite (eqP n12) nds_sol12 nds_sol19 expnS - mulnn 2! mulnA.
     by rewrite (mulnC (ndsC 7)); apply:M.
   move: n12; rewrite ltnS leq_eqVlt; case/orP => n11.
     rewrite (eqP n11) nds_sol11 nds_sol18 -2! mulnn.
     by rewrite mulnCA mulnA (mulnC _ (_ * _)); apply:M.
   move: n11; rewrite ltnS leq_eqVlt; case/orP => n10.
     rewrite (eqP n10) nds_sol10 nds_sol17 mulnCA mulnA.
     by rewrite - mulnn (mulnAC _ _ (ndsC 6)); apply:M.
   move: n10; rewrite ltnS leq_eqVlt; case/orP => n9.
     rewrite (eqP n9) nds_sol9 nds_sol16 - mulnn mulnCA mulnA.
     by apply: (leq_trans (M (ndsC 4) _ _ c47_56)); rewrite mulnC mulnA.
   move: n9; rewrite ltnS leq_eqVlt; case/orP => n8.
    by rewrite (eqP n8) nds_sol8 nds_sol15 - mulnn mulnA.
   move: n8; rewrite ltnS leq_eqVlt; case/orP => n7.
     by rewrite (eqP n7) nds_sol7 nds_sol14 mulnC - mulnn. 
   move: n7; rewrite ltnS leq_eqVlt; case/orP => n6. 
     by rewrite (eqP n6) nds_sol6 nds_sol13 mulnC - mulnn.
   move: n6; rewrite ltnS leq_eqVlt; case/orP => n5.
     by rewrite (eqP n5) nds_sol5 nds_sol12 mulnC.
   move: n5; rewrite ltnS leq_eqVlt; case/orP => n4. 
     by rewrite (eqP n4) nds_sol4 nds_sol11 mulnC - mulnn.
   move: n4; rewrite ltnS leq_eqVlt; case/orP => n3. 
     by rewrite (eqP n3) nds_sol3 nds_sol10 mulnC.
   move: n3; rewrite ltnS leq_eqVlt; case/orP => n2.
    by rewrite (eqP n2) nds_sol2 nds_sol9 mulnC.  
  rewrite - (eqP k7); apply: (Hp n2).
move: k7; rewrite ltnS leq_eqVlt; case/orP => k7.
   rewrite (eqP k7) ltnS leq_eqVlt; case/orP => n19.
      rewrite (eqP n19) nds_sol19 nds_sol25.
      by rewrite expnS - mulnn  2!expnS - mulnn !mulnA.
   move: n19; rewrite ltnS leq_eqVlt; case/orP => n18.
      by rewrite (eqP n18) nds_sol18 nds_sol24 mulnCA - expnS.
   move: n18; rewrite ltnS leq_eqVlt; case/orP => n17.
     by rewrite  (eqP n17) nds_sol17 nds_sol23 mulnC - mulnA mulnn.
   move: n17; rewrite ltnS leq_eqVlt; case/orP => n16.
     by rewrite  (eqP n16) nds_sol16 nds_sol22 mulnC.
   move: n16; rewrite ltnS leq_eqVlt; case/orP => n15.
     rewrite (eqP n15) nds_sol15 nds_sol21 mulnA (mulnC (ndsC 6)).
     by rewrite (expnS _ 3) (expnS _ 2) mulnA; apply: M.
   move: n15; rewrite ltnS leq_eqVlt; case/orP => n14. 
     rewrite (eqP n14) nds_sol14 nds_sol20 - mulnn  expnSr !mulnA.
     apply:(M); rewrite (mulnC (ndsC 6)) (mulnC (ndsC 4) (ndsC 5)).
     by rewrite (mulnAC (ndsC 5)); apply:M.
   move: n14; rewrite ltnS leq_eqVlt; case/orP => n13.
     by rewrite (eqP n13) nds_sol13 nds_sol19.
   move: n13; rewrite ltnS leq_eqVlt; case/orP => n12. 
     by rewrite (eqP n12) nds_sol12 nds_sol18 mulnCA  mulnn.
   move: n12; rewrite ltnS leq_eqVlt; case/orP => n11.
     by rewrite (eqP n11) nds_sol11 nds_sol17 mulnC.
   move: n11; rewrite ltnS leq_eqVlt; case/orP => n10.
     by rewrite (eqP n10) nds_sol10 nds_sol16 mulnC.
   move: n10; rewrite ltnS leq_eqVlt; case/orP => n9.
     rewrite (eqP n9) nds_sol9 nds_sol15 -2! mulnn mulnA (mulnC (ndsC 4)).
     by apply:M; rewrite mulnC.
   move: n9; rewrite ltnS leq_eqVlt; case/orP => n8.
     by rewrite (eqP n8) nds_sol8 nds_sol14 -mulnn. 
   move: n8; rewrite ltnS leq_eqVlt; case/orP => n7.
    by rewrite (eqP n7) nds_sol7 nds_sol13 mulnn.
   move: n7; rewrite ltnS leq_eqVlt; case/orP => n6.
    by rewrite (eqP n6) nds_sol6 nds_sol12 mulnC.
   move: n6; rewrite ltnS leq_eqVlt; case/orP => n5.
     by rewrite (eqP n5) nds_sol5 nds_sol11 mulnC - mulnn.
   move: n5; rewrite ltnS leq_eqVlt; case/orP => n4.
     by rewrite (eqP n4) nds_sol4 nds_sol10 mulnC.
   move: n4; rewrite ltnS leq_eqVlt; case/orP => n3.
    by rewrite (eqP n3) nds_sol3 nds_sol9 mulnC - mulnn.
   move: n3; rewrite ltnS leq_eqVlt; case/orP => n2.
     by rewrite (eqP n2) nds_sol2 nds_sol8 mulnC; apply: Hq.
   by rewrite -(eqP k7);apply: (Hp n2).
move: k7; rewrite ltnS leq_eqVlt; case/orP => k7.
   rewrite (eqP k7) ltnS leq_eqVlt; case/orP => n19.
     by rewrite  (eqP n19) nds_sol19 nds_sol24.
   move: n19; rewrite ltnS leq_eqVlt; case/orP => n18.
     by rewrite (eqP n18) nds_sol18 nds_sol23 mulnA mulnn.
   move: n18; rewrite ltnS leq_eqVlt; case/orP => n17.
     by rewrite (eqP n17) nds_sol17 nds_sol22 mulnA - expnS.
   move: n17; rewrite ltnS leq_eqVlt; case/orP => n16. 
     by rewrite (eqP n16) nds_sol16 nds_sol21 - expnS.
   move: n16; rewrite ltnS leq_eqVlt; case/orP => n15.
    by rewrite (eqP n15) nds_sol15 nds_sol20 mulnCA - expnS.
   move: n15; rewrite ltnS leq_eqVlt; case/orP => n14. 
    by rewrite (eqP n14) nds_sol14 nds_sol19 mulnC - mulnn expnS - mulnn mulnA.
   move: n14; rewrite ltnS leq_eqVlt; case/orP => n13. 
     by rewrite (eqP n13) nds_sol13 nds_sol18. 
   move: n13; rewrite ltnS leq_eqVlt; case/orP => n12. 
     by rewrite (eqP n12) nds_sol12 nds_sol17 mulnA -mulnn.
   move: n12; rewrite ltnS leq_eqVlt; case/orP => n11.
     by rewrite (eqP n11) nds_sol11 nds_sol16 - expnS.
   move: n11; rewrite ltnS leq_eqVlt; case/orP => n10.
     by rewrite (eqP n10) nds_sol10 nds_sol15 mulnC - mulnA mulnn.
   move: n10; rewrite ltnS leq_eqVlt; case/orP => n9.
     by rewrite (eqP n9) nds_sol9 nds_sol14 mulnC.
   move: n9; rewrite ltnS leq_eqVlt; case/orP => n8. 
     by rewrite (eqP n8) nds_sol8 nds_sol13. 
   move: n8; rewrite ltnS leq_eqVlt; case/orP => n7. 
     by rewrite (eqP n7) nds_sol7 nds_sol12. 
   move: n7; rewrite ltnS leq_eqVlt; case/orP => n6.
     by rewrite (eqP n6) nds_sol6 nds_sol11. 
   move: n6; rewrite ltnS leq_eqVlt; case/orP => n5. 
     by rewrite (eqP n5) nds_sol5 nds_sol10 mulnC.
   move: n5; rewrite ltnS leq_eqVlt; case/orP => n4.
     by rewrite (eqP n4) nds_sol4 nds_sol9 mulnC -mulnn.
   move: n4; rewrite ltnS leq_eqVlt; case/orP => n3. 
     by rewrite (eqP n3) nds_sol3 nds_sol8 mulnC.
   move: n3; rewrite ltnS leq_eqVlt; case/orP => n2.
     by rewrite (eqP n2) nds_sol2 nds_sol7 mulnC; apply: Hq.
   by rewrite - (eqP k7); apply: (Hp n2).
move: k7; rewrite ltnS leq_eqVlt; case/orP => k7.
   rewrite (eqP k7) ltnS leq_eqVlt; case/orP => n19.
      rewrite  (eqP n19) nds_sol19 nds_sol23.
      by rewrite expnS mulnA -(mulnn  (ndsC 5)); apply: M.
   move: n19; rewrite ltnS leq_eqVlt; case/orP => n18.
     rewrite (eqP n18) nds_sol18 nds_sol22 - mulnn (mulnCA (ndsC 5)) mulnA.
     by rewrite expnSr - (mulnA (_ ^2)) - mulnn; apply: M.
   move: n18; rewrite ltnS leq_eqVlt; case/orP => n17.
     rewrite (eqP n17) nds_sol17 nds_sol21 mulnA mulnAC (expnS _ 3) (expnS _ 2).
     by rewrite mulnA; apply:M.
   move: n17; rewrite ltnS leq_eqVlt; case/orP => n16.
     by rewrite (eqP n16) nds_sol16 nds_sol20.
   move: n16; rewrite ltnS leq_eqVlt; case/orP => n15.
     by rewrite (eqP n15) nds_sol15 nds_sol19 - mulnn expnS - mulnn !mulnA.
   move: n15; rewrite ltnS leq_eqVlt; case/orP => n14.
     rewrite (eqP n14) nds_sol14 nds_sol18 - 2!mulnn mulnA.
     by rewrite (mulnC (ndsC 5)) mulnA; apply: M.
   move: n14; rewrite ltnS leq_eqVlt; case/orP => n13.
     by rewrite (eqP n13) nds_sol13 nds_sol17 -2!mulnn mulnA; apply: M.
   move: n13; rewrite ltnS leq_eqVlt; case/orP => n12.
    by rewrite (eqP n12) nds_sol12 nds_sol16 mulnA. 
   move: n12; rewrite ltnS leq_eqVlt; case/orP => n11.
    by rewrite (eqP n11) nds_sol11 nds_sol15.
   move: n11; rewrite ltnS leq_eqVlt; case/orP => n10.
    by rewrite (eqP n10) nds_sol10 nds_sol14 mulnA mulnn.
   move: n10; rewrite ltnS leq_eqVlt; case/orP => n9. 
     by rewrite (eqP n9) nds_sol9 nds_sol13 -2! mulnn mulnA.
   move: n9; rewrite ltnS leq_eqVlt; case/orP => n8. 
    by rewrite (eqP n8) nds_sol8 nds_sol12.
   move: n8; rewrite ltnS leq_eqVlt; case/orP => n7.
     by rewrite (eqP n7) nds_sol7 nds_sol11 - mulnn.
   move: n7; rewrite ltnS leq_eqVlt; case/orP => n6. 
     by rewrite (eqP n6) nds_sol6 nds_sol10.
   move: n6; rewrite ltnS leq_eqVlt; case/orP => n5.
     by rewrite (eqP n5) nds_sol5 nds_sol9 mulnn.
   move: n5; rewrite ltnS leq_eqVlt; case/orP => n4.
     by rewrite (eqP n4) nds_sol4 nds_sol8 mulnC.
   move: n4; rewrite ltnS leq_eqVlt; case/orP => n3.
     by rewrite (eqP n3) nds_sol3 nds_sol7 mulnC.
   move: n3; rewrite ltnS leq_eqVlt; case/orP => n2. 
     by rewrite (eqP n2) nds_sol2 nds_sol6 mulnC; apply: Hq.
   by rewrite - (eqP k7); apply:(Hp n2).
move: k7; rewrite ltnS leq_eqVlt; case/orP => k7.
  rewrite (eqP k7) ltnS leq_eqVlt; case/orP => n19.
      rewrite (eqP n19) nds_sol19 nds_sol22.
      by rewrite expnSr mulnA; apply: M; rewrite - mulnn mulnA.
  move: n19; rewrite ltnS leq_eqVlt; case/orP => n18.
    rewrite  (eqP n18) nds_sol18 nds_sol21 mulnA mulnAC - mulnn mulnA expnSr.
    by apply: M. 
   move: n18; rewrite ltnS leq_eqVlt; case/orP => n17.
     rewrite  (eqP n17) nds_sol17 nds_sol20 mulnA mulnAC (expnS _ 2) mulnA.
     by apply: M.
   move: n17; rewrite ltnS leq_eqVlt; case/orP => n16.
      rewrite  (eqP n16) nds_sol16 nds_sol19 expnS mulnA.
       apply: (leq_trans(M ((ndsC 5) ^2) _ _ c35_44)).
       by rewrite -mulnn expnS - mulnn ! mulnA.
   move: n16; rewrite ltnS leq_eqVlt; case/orP => n15.
     rewrite (eqP n15) nds_sol15 nds_sol18 (mulnC (ndsC 5)) - 2! mulnn.
     by rewrite !mulnA; apply: M.
   move: n15; rewrite ltnS leq_eqVlt; case/orP => n14.
      rewrite  (eqP n14) nds_sol14 nds_sol17 mulnA - mulnn.
      by rewrite -mulnn (mulnAC (ndsC 5)) mulnA; apply: M.
   move: n14; rewrite ltnS leq_eqVlt; case/orP => n13.
     rewrite  (eqP n13) nds_sol13 nds_sol16 - mulnn mulnA.
     apply: (leq_trans(M (ndsC 6) _ _ c36_45)).
     by rewrite mulnAC expnSr - mulnn; apply:M.
   move: n13; rewrite ltnS leq_eqVlt; case/orP => n12.
     rewrite  (eqP n12) nds_sol12 nds_sol15 mulnA mulnAC - mulnn mulnA.
     by apply: (leq_trans(M (ndsC 5) _ _ c36_45)).
   move: n12; rewrite ltnS leq_eqVlt; case/orP => n11. 
     rewrite  (eqP n11) nds_sol11 nds_sol14 - mulnn - mulnn ! mulnA.
     by apply: (leq_trans(M (ndsC 5) _ _ c35_44)).
   move: n11; rewrite ltnS leq_eqVlt; case/orP => n10. 
     by rewrite  (eqP n10) nds_sol10 nds_sol13 mulnA - mulnn.
   move: n10; rewrite ltnS leq_eqVlt; case/orP => n9.
     by rewrite  (eqP n9) nds_sol9 nds_sol12 - mulnn mulnA.
   move: n9; rewrite ltnS leq_eqVlt; case/orP => n8.
     by rewrite (eqP n8) nds_sol8 nds_sol11 - mulnn.
   move: n8; rewrite ltnS leq_eqVlt; case/orP => n7.
     by rewrite (eqP n7) nds_sol7 nds_sol10. 
   move: n7; rewrite ltnS leq_eqVlt; case/orP => n6.
    by rewrite (eqP n6) nds_sol6 nds_sol9 - mulnn.
   move: n6; rewrite ltnS leq_eqVlt; case/orP => n5.
     by rewrite (eqP n5) nds_sol5 nds_sol8.
   move: n5; rewrite ltnS leq_eqVlt; case/orP => n4.
     by rewrite (eqP n4) nds_sol4 nds_sol7.
   move: n4; rewrite ltnS leq_eqVlt; case/orP => n3.
     by rewrite (eqP n3) nds_sol3 nds_sol6 mulnC.
   move: n3; rewrite ltnS leq_eqVlt; case/orP => n2.
     by rewrite (eqP n2) nds_sol2 nds_sol5 mulnC; apply: Hq.
   rewrite -(eqP k7); apply: (Hp n2).
move: k7; rewrite ltnS leq_eqVlt; case/orP => k7.
  rewrite (eqP k7).
  rewrite ltnS leq_eqVlt; case/orP => n19.
      rewrite  (eqP n19) nds_sol19 nds_sol21 expnS mulnA.
      apply: (leq_trans (M (ndsC 6 ^ 2) _ _ c26_35)).
      rewrite mulnAC (expnSr _ 3); apply: (M).
      rewrite - mulnn mulnA;apply:(leq_trans (M (ndsC 6) _ _ c36_45)).
      by rewrite mulnAC expnS - mulnn mulnA; apply:M.
  move: n19; rewrite ltnS leq_eqVlt; case/orP => n18.
    rewrite (eqP n18) nds_sol18 nds_sol20 mulnCA mulnC - mulnn.
    rewrite  expnSr mulnA mulnA; apply: (M).
     apply: (leq_trans (M (ndsC 6) _ _ c26_35)).
     rewrite mulnAC -mulnn mulnA; apply: (M (ndsC 5) _ _ (c36_45)).
  move: n18; rewrite ltnS leq_eqVlt; case/orP => n17.
    rewrite  (eqP n17) nds_sol17 nds_sol19 mulnA - mulnn expnSr mulnA.
    by apply:M. 
  move: n17; rewrite ltnS leq_eqVlt; case/orP => n16.
      rewrite  (eqP n16) nds_sol16 nds_sol18 expnSr mulnA (mulnC (ndsC 5)).
      by apply: M; rewrite - mulnn mulnA -mulnn.
  move: n16; rewrite ltnS leq_eqVlt; case/orP => n15.
     rewrite  (eqP n15) nds_sol15 nds_sol17 mulnA (mulnC _ (ndsC 6)).
     by apply: M.     
  move: n15; rewrite ltnS leq_eqVlt; case/orP => n14.
     rewrite  (eqP n14) nds_sol14 nds_sol16 mulnA - mulnn expnSr - mulnn mulnA.
     apply: (M); apply (leq_trans (M (ndsC 4) _ _ c24_6)).
     by rewrite mulnC.
  move: n14; rewrite ltnS leq_eqVlt; case/orP => n13.
     rewrite  (eqP n13) nds_sol13 nds_sol15 - !mulnn mulnA mulnA. 
     apply (leq_trans (M (ndsC 6) _ _ c26_35)).
     by rewrite mulnAC; apply: M.
  move: n13; rewrite ltnS leq_eqVlt; case/orP => n12.
     rewrite  (eqP n12) nds_sol12 nds_sol14 - mulnn mulnA mulnAC.
     by apply: M.
  move: n12; rewrite ltnS leq_eqVlt; case/orP => n11. 
    by rewrite (eqP n11) nds_sol11 nds_sol13 -mulnn mulnA.
   move: n11; rewrite ltnS leq_eqVlt; case/orP => n10. 
     rewrite (eqP n10) nds_sol10 nds_sol12 mulnA (mulnC _ (ndsC 6)).
     by apply: M.
   move: n10; rewrite ltnS leq_eqVlt; case/orP => n9.
     rewrite (eqP n9) nds_sol9 nds_sol11 - mulnn - mulnn mulnA.
     by apply: (leq_trans (M (ndsC 4) _ _ c24_6)); rewrite mulnC.
   move: n9; rewrite ltnS leq_eqVlt; case/orP => n8.
     by rewrite (eqP n8) nds_sol8 nds_sol10.
   move: n8; rewrite ltnS leq_eqVlt; case/orP => n7.
     by rewrite (eqP n7) nds_sol7 nds_sol9 - mulnn.
   move: n7; rewrite ltnS leq_eqVlt; case/orP => n6.
     by rewrite (eqP n6) nds_sol6 nds_sol8.
   move: n6; rewrite ltnS leq_eqVlt; case/orP => n5.
     by rewrite (eqP n5) nds_sol5 nds_sol7. 
   move: n5; rewrite ltnS leq_eqVlt; case/orP => n4.
     by rewrite (eqP n4) nds_sol4 nds_sol6.
   move: n4; rewrite ltnS leq_eqVlt; case/orP => n3.
      by rewrite (eqP n3) nds_sol3 nds_sol5.
   move: n3; rewrite ltnS leq_eqVlt; case/orP => n2.
     by rewrite (eqP n2) nds_sol2 nds_sol4 mulnC; apply: Hq.
   rewrite -(eqP k7); apply: (Hp n2).
move: k7; rewrite ltnS leq_eqVlt; case/orP => k7; last first.
  move => _; move: k7; rewrite ltnS leqn0 => /eqP ->. rewrite ndsC0 mul1n addn0.
  rewrite leqnn; exact: isT.
rewrite (eqP k7) ltnS leq_eqVlt; case/orP => n19.
     rewrite (eqP n19) nds_sol19 nds_sol20 expnS mulnA.
     apply: (leq_trans (M (ndsC 6 ^ 2) _ _ (Hq 6 isT))).
     rewrite - mulnn mulnA (mulnC (ndsC 7)).
     apply: (leq_trans (M (ndsC 6) _ _ (c67_445))).
     rewrite expnSr mulnA mulnAC; apply: (M).
     by rewrite - mulnA mulnC (mulnC _  (_ ^ 2)) - mulnn; apply: M.
   move: n19; rewrite ltnS leq_eqVlt; case/orP => n18.
     rewrite (eqP n18) nds_sol18 nds_sol19 mulnA (expnS _ 2).
     by apply: M; apply: Hq.
   move: n18; rewrite ltnS leq_eqVlt; case/orP => n17.
     rewrite (eqP n17) nds_sol17 nds_sol18 - mulnn - mulnn (mulnCA (ndsC 5)).
     by rewrite mulnA mulnA - (mulnA _ _ (ndsC 6)); apply: M; apply: Hq.
   move: n17; rewrite ltnS leq_eqVlt; case/orP => n16.
     rewrite (eqP n16) nds_sol16 nds_sol17 expnS mulnA (mulnC _ (ndsC 6)).
     by apply: M; apply: Hq.
   move: n16; rewrite ltnS leq_eqVlt; case/orP => n15.
     rewrite (eqP n15) nds_sol15 nds_sol16 (expnS _ 2) mulnA. 
     by apply: M; apply: Hq.
   move: n15; rewrite ltnS leq_eqVlt; case/orP => n14.
      rewrite (eqP n14) nds_sol14 nds_sol15 - mulnn - mulnn.
      rewrite mulnA mulnA mulnCA - (mulnA  _ _ (ndsC 5)).
      by apply: M; apply: Hq.
   move: n14; rewrite ltnS leq_eqVlt; case/orP => n13.
      rewrite (eqP n13) nds_sol13 nds_sol14 - mulnn - mulnn mulnA.
      by apply: (leq_trans (M (ndsC 6) _ _ (Hq 6 isT))); rewrite mulnC.
   move: n13; rewrite ltnS leq_eqVlt; case/orP => n12.
     rewrite (eqP n12) nds_sol12 nds_sol13 mulnA - mulnn.
     by apply: M; apply: Hq.
   move: n12; rewrite ltnS leq_eqVlt; case/orP => n11.
     rewrite (eqP n11) nds_sol11 nds_sol12 - mulnn mulnA (mulnC (ndsC 5)).
     by apply: M; apply: Hq.
   move: n11; rewrite ltnS leq_eqVlt; case/orP => n10.
     rewrite (eqP n10) nds_sol10 nds_sol11 - mulnn mulnA.
     by apply: M; apply: Hq.
   move: n10; rewrite ltnS leq_eqVlt; case/orP => n9.
     rewrite (eqP n9) nds_sol9 nds_sol10  - mulnn mulnA (mulnC (ndsC 4)).
     by apply: M; apply: Hq.
   move: n9; rewrite ltnS leq_eqVlt; case/orP => n8.
     by rewrite (eqP n8) nds_sol8 nds_sol9; apply: c17_44.
  move: n8; rewrite ltnS leq_eqVlt; case/orP => n7.
     by rewrite (eqP n7) nds_sol7 nds_sol8; apply: Hq.
   move: n7; rewrite ltnS leq_eqVlt; case/orP => n6.
     by rewrite (eqP n6) nds_sol6 nds_sol7; apply: Hq.
   move: n6; rewrite ltnS leq_eqVlt; case/orP => n5.
     by rewrite (eqP n5) nds_sol5 nds_sol6; apply: Hq.
   move: n5; rewrite ltnS leq_eqVlt; case/orP => n4.
     by rewrite (eqP n4) nds_sol4 nds_sol5; apply: Hq.
   move: n4; rewrite ltnS leq_eqVlt; case/orP => n3.
     by rewrite (eqP n3) nds_sol3 nds_sol4; apply: Hq.
   move: n3; rewrite ltnS leq_eqVlt; case/orP => n2. 
     by rewrite (eqP n2) nds_sol2 nds_sol3; apply: Hq.
   rewrite -(eqP k7); apply: (Hp n2).
Qed.


Lemma nds_sol_bd n k: 2 <= n -> 0 < k < n ->
    (ndsC k) * (nds_sol (n - k)) <= nds_sol n.
Proof.
move => ha /andP [kp lkn].
rewrite -{2}  (subnK (ltnW lkn)).
have: 0 < n - k by rewrite subn_gt0.
move:(n-k). clear n ha  kp lkn.
pose P k := forall n, 0 <n -> ndsC k * nds_sol n <= nds_sol (n + k).
rewrite -/(P k); move: k.
have Hb q: 4 <= q -> ndsC (q .*2.+1) < ndsC q * ndsC q.+1.
  move => le4q.
  have qp: 0 < q by move: le4q; case q.
  rewrite !ndsCE /ndsCb.
  set t := 2 ^ q.-1.
  have tp:  0 <  t by rewrite  expn_gt0.
  have tp':  0 <  2 ^q  by rewrite  expn_gt0.
  have ->: 2 ^ q.*2 = 2^(q.+1) * t.
    by rewrite - addnn -{2} (prednK qp) - addSnnS expnD.
  have le1: q.*2.+1 * 2 * 2 ^ q <= q * q.+1 * 2 ^ q.
    rewrite (leq_pmul2r tp') mulSn (mulnS q).
    apply: (leq_add (ltnW (ltnW le4q))). rewrite - muln2 - mulnA.
    by rewrite (leq_pmul2l).
  rewrite (mulSnr (q*t)) mulnSr addnS ltnS  - {2}[in 2^q] (prednK qp). 
  rewrite !expnS (mulnAC q t) - mulnDl ! mulnA - mulnDl (ltn_pmul2r tp).
  apply:(leq_ltn_trans  le1).
  by rewrite -addn1 - addnA leq_add2l -{1} (prednK qp) addSn ltnS.
have Ha q: 4 <= q -> ndsC (q .*2) < ndsC q * ndsC q.
  move => le4q.
  have qp: 0 < q by move: le4q; case (q).
  rewrite !ndsCE /ndsCb. 
  set t := 2 ^ q.-1.
   have qtp:  0 < q * t by rewrite muln_gt0 qp expn_gt0.
   have -> : 2 ^ q.*2.-1 = (t *t).*2.
     by rewrite - (prednK qp) doubleS expnS - addnn expnD mul2n. 
   have  ->: q.*2 * (t * t).*2 = (q * t) * (t * 4).
      by rewrite - !muln2 - mulnA (mulnC 2) -[4]/(2 *2) !mulnA.
   rewrite (mulnSr (q * t).+1) addnS ltnS - mulSnr mulnC.
   by rewrite (ltn_pmul2r qtp) ltnS ltnW // ltnS mulnC leq_mul.
have h: (forall k, k <=7 -> P k).
  move => k lk7 n.
  elim: n {1 3 4 5} n (leqnn n).
    by move => n; rewrite  leqn0 => /eqP ->. 
  move => n Hr m; rewrite leq_eqVlt ltnS; case/orP; last by apply: Hr.
  move /eqP ->.
  case: (ltnP n.+1 20) => n20; first by  move => _; apply: nds_sol_aux.
  have n5: 5 <= n.+1 by apply: leq_trans n20.
  have sn5: 0 < n.+1 - 5.
    by rewrite  -(leq_add2r 5) (subnK n5); apply: leq_trans n20.
  move: (subnK n5) => dv _.
  have dkv: n.+1 + k - 5 + 5 = n.+1 + k.
     by rewrite (addnC n.+1 k) - (addnBA _ n5) - addnA dv.
  have n15: 14 < n.+1 - 5 by rewrite - (leq_add2r 5) dv.
  have nk15: 14 < (n.+1 + k) - 5.
    rewrite - (leq_add2r 5) dkv; apply: (leq_trans n20); apply: leq_addr.
  have ltrec: n.+1 - 5 <= n by rewrite - (leq_add2r 5) dv -addn1 leq_add2l.
  rewrite - dkv (nds_sol_rec5 nk15) -{1} dv (nds_sol_rec5 n15) mulnCA leq_mul2l.
  by rewrite (addnC n.+1 k) -(addnBA _ n5) addnC (Hr _ ltrec sn5) orbT.
move => k; elim: k {1 3} (k) (leqnn k).
  by move => k; rewrite leqn0 => /eqP ->; apply: h.
move => n Hr k; rewrite leq_eqVlt ltnS; case /orP; last by apply: Hr.
move /eqP ->.
case: (ltnP n 7); [by apply: h | rewrite -ltnS; move => n7].
have lnn:  n < n.*2.
   by rewrite - addn1 - addnn leq_add2l - ltnS; apply: leq_trans n7.
move:(odd_double_half (n.+1)); case: odd.
  set q := (n.+1)./2; rewrite add1n => qv.
  have /Hb : 3 < q by rewrite - leq_Sdouble qv.
  rewrite qv => /ltnW lt1.
  move => m mp.
  have aux: 0 < m + q.+1 by  rewrite addnS ltnS.
  apply: (@leq_trans (ndsC q * (ndsC q.+1 * (nds_sol m)))).
    by rewrite mulnA leq_mul2r lt1 orbT.
  have la: q.+1 <= n by  rewrite  - ltn_double qv. 
  move: (Hr q (ltnW la) (m + q.+1) aux); rewrite -addnA addSn addnn qv.
  by apply: leq_trans; rewrite leq_mul2l  (Hr q.+1 la _ mp) orbT.
set q := (n.+1)./2; rewrite add0n => qv.
have /Ha : 3 < q by rewrite - leq_double qv.
rewrite qv => /ltnW lt1 m mp.
have aux: 0 < m + q by apply: (leq_trans mp); apply: leq_addr.
apply: (@leq_trans (ndsC q * (ndsC q * (nds_sol m)))).
  by rewrite mulnA leq_mul2r lt1 orbT.
have la: q <= n  by rewrite - leq_double - ltnS qv ltnS. 
move: (Hr q la  _ aux); rewrite -addnA addnn qv.
by  apply: leq_trans; rewrite leq_mul2l  (Hr q la m mp) orbT.
Qed.


Lemma nds_alt (f: nat -> nat) (c:= ndsC) :
  f 0 = 1 -> f 1 = 1 ->  
  (forall n,   2 <= n -> 
               exists2 k, 0 < k < n & f n <= (c k) * (f (n - k))) ->
  (forall n,  nds_sol n.+1 <= f n.+1) ->
  (forall n,  nds_sol n = f n).
Proof.
move => HF0 HF1 HFle HFge.
move => n; move: (leqnn n); elim: n {- 2} (n).
  by move => n; rewrite leqn0 => /eqP ->; rewrite nds_sol0 HF0.
move => n Hr p; rewrite leq_eqVlt; case/orP; last by rewrite ltnS => /Hr.
move/eqP ->.
apply: anti_leq; rewrite HFge.
case:(posnP n); first by move ->;  rewrite nds_sol1 HF1.
rewrite - ltnS;move => np.
move: (HFle _ np) => [k klt kv]; apply: (leq_trans kv).
move: (@nds_sol_bd _ _  np  klt).
move/andP: klt => [kp ]; rewrite ltnS => kn1.
by rewrite (subSn kn1) - Hr // - (subSn kn1) leq_subLR -{1}(add0n n) ltn_add2r.
Qed.


End Nds.


