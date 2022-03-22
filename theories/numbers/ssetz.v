 (** * The set Z of rational integers
  Copyright INRIA (2009-2014 2018) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: ssetz.v,v 1.7 2018/10/01 14:40:54 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module RationalIntegers.
(** ** The set of rational integers *)

(** Z is the disjoint union of N* and N; [J x C1] is positive, [J y C0] is negative *)

  
(** We define 0 and the injections [N -> Zp] and [N -> Zm] *)

Definition BZ_of_nat x := J x C1.

Notation BZ_val := P (only parsing).
Notation BZ_sg := Q (only parsing).

(** We define 0 1 2 3 4 and -1 as elements of Z *)

Definition BZ_zero := BZ_of_nat \0c.
Definition BZ_one := BZ_of_nat \1c.
Definition BZ_two := BZ_of_nat \2c.
Definition BZ_three := BZ_of_nat \3c.
Definition BZ_four := BZ_of_nat \4c.

Notation "\0z" := BZ_zero.
Notation "\1z" := BZ_one.
Notation "\2z" := BZ_two.
Notation "\3z" := BZ_three.
Notation "\4z" := BZ_four.


Definition BZm_of_nat x := Yo (x = \0c) \0z (J x C0).
Definition BZ_mone := BZm_of_nat \1c.
Notation "\1mz" := BZ_mone.


(** We define Z Zp Zm Zps Zms and Ns (p=positive, m=negative s = nonzero) *)

Definition Nats:= Nat -s1 \0c.
Definition BZ := canonical_du2 Nats Nat.
Definition BZms:= Nats *s1 C0.
Definition BZp:=  Nat *s1 C1.
Definition BZps:= Nats *s1 C1.
Definition BZm:= BZms +s1 \0z.
Definition BZs := BZ -s1 \0z.
Definition intp x := inc x BZ.

Definition int_pp x := BZ_sg x = C1.
Definition int_np x := BZ_sg x = C0.

(** We show that some sets are subsets of others *) 

Lemma BZp_sBZ x : inc x BZp -> intp x.
Proof. 
by move => /indexed_P [pa pb pc]; rewrite - pa pc; apply :candu2_prb.
Qed.

Lemma BZps_sBZp : sub BZps BZp.
Proof. 
by move => t /indexed_P [pa] /setC1_P [pb pc] pd; apply indexed_P.
Qed.

Lemma BZps_sBZ x:inc x BZps -> intp x.
Proof. apply: (sub_trans BZps_sBZp BZp_sBZ). Qed.

Lemma BZms_sBZm : sub BZms BZm.
Proof. by move => t ts; apply /setU1_P; left. Qed.

Lemma BZms_sBZ x:inc x BZms -> intp x.
Proof. 
by move => /indexed_P [pa pb pc]; rewrite - pa pc; apply :candu2_pra.
Qed.

Lemma BZm_sBZ x:inc x BZm -> intp x.
Proof. 
case /setU1_P; first by apply: BZms_sBZ. 
move => ->; apply :candu2_prb; apply: NS0.
Qed.


(** We show that the injections have values in Zp and Zm *)

Lemma BZ_of_natp_i x: natp x -> inc (BZ_of_nat x) BZp.
Proof. by move => xN; apply: indexed_pi. Qed.

Lemma BZ_of_nat_i x: natp x -> intp (BZ_of_nat x).
Proof. by move => xN;apply:BZp_sBZ;apply:BZ_of_natp_i. Qed.

Lemma BZm_of_natms_i x: natp x -> x <> \0c ->
  inc (BZm_of_nat x) BZms.
Proof. 
by move => xN xnz;rewrite /BZm_of_nat; Ytac0; apply: indexed_pi;apply /setC1_P.
Qed.

Lemma BZm_of_natm_i x: natp x -> inc (BZm_of_nat x) BZm.
Proof. 
move => xN; rewrite /BZm_of_nat; Ytac xnz; first by apply /setU1_P; right.
by apply /setU1_P; left; apply: indexed_pi; apply /setC1_P.
Qed.

Lemma BZm_of_nat_i x: natp x -> intp (BZm_of_nat x).
Proof. move => h; exact: (BZm_sBZ (BZm_of_natm_i h)). Qed.

Lemma BZ0_val: BZ_val \0z = \0c.
Proof. by rewrite /BZ_zero /BZ_of_nat;aw. Qed.
 
Lemma BZ0_sg: int_pp \0z.
Proof. by  rewrite /BZ_zero /int_pp /BZ_of_nat;aw. Qed.
 
Lemma BZps_valnz x: inc x BZps -> BZ_val x <> \0c.
Proof. by move /indexed_P => [_] /setC1_P [_]. Qed.

Lemma BZps_iP x: inc x BZps <-> (inc x BZp /\ x <> \0z).
Proof. 
split.
  move => /indexed_P [pa ] /setC1_P [pb pc] pd;split => //. 
    by apply /indexed_P.
  by dneg pe; rewrite pe BZ0_val.
move => [] /indexed_P [pa pb pc] pd; apply /indexed_P;split => //. 
apply /setC1_P;split => //.
dneg pe;rewrite /BZ_zero /BZ_of_nat; apply: pair_exten;aww.
Qed.

Lemma BZms_nz  x: inc x BZms -> x <> \0z.
Proof. move => /indexed_P [_ _ h2] h; move: h2;rewrite h BZ0_sg; fprops. Qed.

Lemma BZps_nz x: inc x BZps -> x <> \0z.
Proof.  by case /BZps_iP. Qed.

Lemma BZms_iP x: inc x BZms <-> (inc x BZm /\ x <> \0z).
Proof.
split; last by move => [] /setU1_P; case.
by move => h; move: (BZms_nz h)=> xnz;split => //; apply /setU1_P;left.
Qed.



(** We show that [N -> Zp] and [N -> Zm] are injective *)

Lemma BZ_of_nat_val x: BZ_val (BZ_of_nat x) = x.
Proof. by rewrite /BZ_of_nat; aw. Qed.

Lemma BZm_of_nat_val x: BZ_val (BZm_of_nat x) = x.
Proof. by rewrite /BZm_of_nat; Ytac xz; aw => //; rewrite BZ0_val xz. Qed.

Lemma BZ_of_nat_inj x y: BZ_of_nat x = BZ_of_nat y -> x = y.
Proof. by move => /pr1_def. Qed.

Lemma BZm_of_nat_inj x y:  BZm_of_nat x = BZm_of_nat y -> x = y.
Proof. by move => h; move: (f_equal P h); rewrite ! BZm_of_nat_val. Qed.

Lemma BZm_of_nat_inj_bis x y: BZm_of_nat x = BZ_of_nat y -> (x = y /\ x = \0c).
Proof. 
rewrite / BZm_of_nat; Ytac xz.
   by move => h; move: (f_equal P h);rewrite xz /BZ_zero /BZ_of_nat;aw.
by move => h; move: (f_equal Q h); rewrite /BZ_of_nat;aw => bad; case: C0_ne_C1.
Qed.

Lemma BZ_0_if_val0 x: intp x -> BZ_val x = \0c -> x = \0z.
Proof.
move /candu2P => [pa]; case; first by move => [] /setC1_P [].
move => [_ pb] pc; rewrite/BZ_zero /BZ_of_nat; apply: pair_exten;aw; fprops.
Qed.


(** We show that 0, 1, etc are rational integers *)
Lemma ZS0 : intp \0z.
Proof. apply:BZ_of_nat_i; apply: NS0. Qed.

Lemma ZpS0 : inc \0z BZp.
Proof. apply: indexed_pi; apply:NS0. Qed.

Lemma ZmS0 : inc \0z BZm.
Proof. by apply /setU1_P; right. Qed.

Lemma ZS1 : intp \1z.
Proof. apply:BZ_of_nat_i; apply:NS1. Qed.

Lemma ZpsS1 : inc \1z BZps.
Proof. apply: indexed_pi; apply /setC1_P;split; fprops;apply:NS1. Qed.

Lemma ZS2 : intp \2z.
Proof. apply:BZ_of_nat_i; apply: NS2. Qed.

Lemma ZS3 : intp \3z.
Proof. apply:BZ_of_nat_i; apply: NS3. Qed.

Lemma ZS4 : intp \4z.
Proof.  apply:BZ_of_nat_i; apply: NS4. Qed.

Lemma ZpsS4 : inc \4z BZps.
Proof.  
apply: indexed_pi; apply /setC1_P;split; fprops; first apply:NS4.
apply: succ_nz.
Qed.

Lemma ZSm1 : intp \1mz.
Proof. apply:BZm_of_nat_i; apply: NS1. Qed.

Lemma ZmsS_m1: inc \1mz BZms.
Proof. apply:BZm_of_natms_i; fprops;apply: NS1. Qed.

Lemma ZpsS2: inc \2z BZps.
Proof. apply: indexed_pi; apply /setC1_P;split; fprops;apply:NS2. Qed.

Lemma BZ1_nz: \1z <> \0z.
Proof. by move/pr1_def; fprops. Qed.

Lemma BZm1_nz: \1mz <> \0z.
Proof. 
rewrite /BZ_mone /BZm_of_nat; Ytac k; first by case: card1_nz.
move => /pr1_def; fprops.
Qed.


(**  More properties of integers *)

Lemma BZ_valN a: intp a -> natp (BZ_val a).
Proof.  by move /candu2P => [_]; case => [] [] // /setC1_P []. Qed.

Lemma BZ_sgv x: intp x -> (int_np x \/ int_pp x).
Proof. apply: candu2_pr2. Qed.


Lemma BZp_sg x: inc x BZp -> int_pp x.
Proof. by move /indexed_P => [_]. Qed.

Lemma BZps_sg x: inc x BZps -> int_pp x.
Proof.  by move /indexed_P => [_]. Qed.

Lemma BZms_sg x: inc x BZms -> int_np x.
Proof.  by move /indexed_P => [_].  Qed. 

Lemma BZms_hi_pr x: inc x BZms -> 
   (BZ_val x <> \0c /\ BZm_of_nat (BZ_val x) = x).
Proof. 
move /indexed_P => [pa] /setC1_P [pb pc] pd;split => //.
by rewrite /BZm_of_nat; Ytac0; rewrite - {2} pa pd.
Qed.

Lemma BZp_hi_pr x: inc x BZp -> BZ_of_nat (BZ_val x) = x.
Proof. by move /indexed_P => [pa pb pc]; rewrite /BZ_of_nat -{2} pa pc. Qed.

Lemma BZm_hi_pr x: inc x BZm -> BZm_of_nat (BZ_val x) = x.
Proof. 
rewrite /BZm_of_nat;case /setU1_P.
  by move /indexed_P => [pa] /setC1_P [pb pc] pd; Ytac0; rewrite  -{2} pa pd.
by move => ->; rewrite BZ0_val; Ytac0.
Qed.

Lemma BZ_hi_pr a: intp a -> 
  a =  BZ_of_nat (BZ_val a) \/ a =  BZm_of_nat (BZ_val a).
Proof. 
move /candu2P => [pa] [] [pb pc]. 
  right; symmetry; apply:BZm_hi_pr; apply /setU1_P; left.
  by apply/ indexed_P.
by left; symmetry; apply BZp_hi_pr; apply/ indexed_P.
Qed.


(** We have a partition of Z as Zp and Zms, but there are more such partitions *)

 
Lemma BZ_i0P x: intp x <-> (inc x  BZms \/ inc x BZp).
Proof.  
split; last by case => h; [apply:BZms_sBZ | apply:BZp_sBZ].
move /candu2P => [pa] [] [pb pc]. 
+ by left; rewrite -pa pc; apply: indexed_pi.
+ by right;rewrite -pa pc; apply: indexed_pi.
Qed.

Lemma BZ_i1P x: intp x  <-> [\/ x = \0z, inc x BZps | inc x BZms].
Proof.
split.
   move /BZ_i0P; case => h; first by constructor 3.
   case: (equal_or_not x \0z); first by constructor 1. 
   by constructor 2; apply /BZps_iP.
case; [move ->; apply:ZS0 | apply:BZps_sBZ | apply:BZms_sBZ].
Qed.

Lemma BZ_i2P x: intp x <-> (inc x  BZps \/ inc x BZm).
Proof.
split; last by case; [apply:BZps_sBZ | apply:BZm_sBZ].
case /BZ_i1P; [by move => ->; right; apply /setU1_P;right | by left | right ].
by apply /setU1_P;left.
Qed.

Lemma BZs_prop: BZs = BZms \cup BZps.
Proof.
set_extens t.
  move =>/setC1_P [/BZ_i1P h xz]; apply /setU2_P; case: h; fprops.
  by move => tz; case: xz.
move => /setU2_P; case. 
+ by move/BZms_iP => [sa sb]; apply/setC1_P; split=> //; apply:BZm_sBZ.
+ by move/BZps_iP => [sa sb]; apply/setC1_P; split => //; apply:BZp_sBZ.
Qed.

Lemma BZ_di_neg_pos x: inc x BZms -> inc x BZp -> False.
Proof.
move => h1 h2; move : (BZms_sg h1). rewrite /int_np (BZp_sg h2); fprops.
Qed.

Lemma BZ_di_pos_neg x: inc x  BZps -> inc x BZm -> False.
Proof. 
move /BZps_iP=> [p1 p2]; case /setU1_P => // p3; apply: (BZ_di_neg_pos p3 p1).
Qed.

Lemma BZ_di_neg_spos x: inc x  BZms -> inc x BZps -> False.
Proof. 
move => h; move:(BZms_sBZm h) =>h1 h2; apply:BZ_di_pos_neg h2 h1.
Qed.


Lemma BZp_i a : intp a ->  int_pp a -> inc a BZp.
Proof. 
by move => az ap; case /BZ_i0P: az => // h; case:C0_ne_C1;rewrite - (BZms_sg h).
Qed.

Lemma BZms_i a : intp a -> int_np a -> inc a BZms.
Proof. 
by move => az ap; case /BZ_i0P: az => // h; case:C0_ne_C1;rewrite - (BZp_sg h).
Qed.

(** We show that Ns and Z are infinite countable *)

Lemma cardinal_Nats: cardinal Nats = aleph0.
Proof. 
symmetry; rewrite aleph0_pr1.
apply card_setC1_inf; apply: infinite_Nat.
Qed.

Lemma cardinal_BZ: cardinal BZ = aleph0.
Proof.
have ->: cardinal BZ = Nats +c Nat by [].
by rewrite - csum2cl cardinal_Nats aleph0_pr2. 
Qed.

(** ** Opposite *)

(** The oppositive of a number is obtained by swapping C0 and C1 in the second component, except for zero *)

Definition BZopp x:=  
  Yo (int_np x) (BZ_of_nat (BZ_val x)) (BZm_of_nat (BZ_val x)).

Definition BZopp_fun := Lf BZopp BZ BZ.

Lemma ZSo x: intp x -> intp (BZopp x).
Proof.
move => xz; move: (BZ_valN xz) => pB.
rewrite /BZopp; Ytac aux; [ by apply:BZ_of_nat_i | by apply:BZm_of_nat_i ].
Qed.

Lemma BZopp_0 : BZopp \0z = \0z.
Proof. 
rewrite /BZopp /int_np {1} /BZ_zero /BZ_of_nat; aw; Ytac0.
by rewrite BZ0_val / BZm_of_nat; Ytac0.
Qed.

(** Oppositive maps Zp to Zm and Zps to Zms. It is an involution of Z  *)

Lemma BZopp_val x: BZ_val (BZopp x) = BZ_val x.
Proof. 
rewrite /BZopp; Ytac sx; first by rewrite BZ_of_nat_val.
by rewrite  BZm_of_nat_val.
Qed.

Lemma BZnon_zero_opp x: intp x ->  (x <> \0z <-> BZopp x <> \0z).
Proof. 
move => xz;apply:iff_neg; split => h; first by rewrite h BZopp_0.
by apply: (BZ_0_if_val0 xz); rewrite - (BZopp_val x) h BZ0_val.
Qed.

Lemma BZopp_sg x: intp x -> x <> \0z ->
   ((int_np x -> int_pp (BZopp x))
     /\ (int_pp x -> int_np (BZopp x))).
Proof.
move => pa pb; rewrite /int_np /int_pp.
have pnz: (P x <> \0c) by move => h; case: pb; apply: BZ_0_if_val0.
by rewrite /BZopp /BZ_of_nat /BZm_of_nat; Ytac0;Ytac sx; aw; rewrite ? sx. 
Qed.

Lemma BZopp_positive1 x: inc x BZps -> inc (BZopp x) BZms.
Proof.
move /BZps_iP => [pa pb]; move: (BZp_sg pa)(BZp_sBZ pa) => h1 h2.
apply: (BZms_i (ZSo h2)) (proj2 (BZopp_sg h2 pb) h1).
Qed.

Lemma BZopp_positive2 x: inc x BZp -> inc (BZopp x) BZm.
Proof.
case:(equal_or_not x  \0z); first by move => -> _; rewrite BZopp_0; apply:ZmS0.
by move => pa pb;apply /setU1_P; left; apply BZopp_positive1; apply /BZps_iP. 
Qed.

Lemma BZopp_negative1 x: inc x BZms -> inc (BZopp x) BZps.
Proof. 
move => xn; move : (BZms_sBZ xn) => xz.
move: (BZms_nz xn) => xnz ;apply/ BZps_iP; split.
  exact: (BZp_i (ZSo xz) (proj1 (BZopp_sg xz xnz)  (BZms_sg xn))).
by apply /(BZnon_zero_opp xz).
Qed. 

Lemma BZopp_negative2 x: inc x BZm -> inc (BZopp x) BZp.
Proof. 
case /setU1_P => h; first by move: (BZopp_negative1 h) => /BZps_iP [].
by rewrite h BZopp_0; apply: ZpS0.
Qed.

Lemma BZopp_K x: intp x -> BZopp (BZopp x) = x.
Proof. 
move => xz.
move: C0_ne_C1 => ns.
rewrite {1} /BZopp BZopp_val /BZopp; case: (equal_or_not(Q x) C0) => h; Ytac0.
  rewrite /BZ_of_nat/int_np; aw; Ytac0;apply:BZm_hi_pr.
  move/candu2P: xz => [px]; case; last by move => [_]; rewrite h.
  move => [pa pb];apply /setU1_P;left;apply /indexed_P;split => //.
rewrite /BZm_of_nat /int_np; case: (equal_or_not (P x) \0c) => h1; Ytac0.
  by rewrite BZ0_sg; Ytac0; symmetry;apply: BZ_0_if_val0.
aw;Ytac0; apply:BZp_hi_pr; move/candu2P: xz => [px]; case; first by move => [_].
by move => [pa pb]; apply /indexed_P.
Qed.

Lemma BZopp_inj a b: intp a -> intp b -> BZopp a = BZopp b -> a = b.
Proof. 
by move => az bz h;rewrite - (BZopp_K az) h (BZopp_K bz).  
Qed.

Lemma BZopp_fb: bijection (Lf BZopp BZ BZ).
Proof. 
apply: lf_bijective.
- by move => t /ZSo.
- apply: BZopp_inj.
- by move => y yz; exists (BZopp y); [apply:ZSo | rewrite (BZopp_K yz)].
Qed.


Lemma BZopp_perm: inc (Lf BZopp BZ BZ) (permutations BZ).
Proof. 
have h:= BZopp_fb; have h1:= (proj1 (proj1 h)).
by apply: Zo_i => //; apply/functionsP; split => //; rewrite/BZopp_fun; aw.
Qed.         

Lemma BZopp_p x: BZopp (BZ_of_nat x) = BZm_of_nat x.
Proof. by rewrite /BZopp /BZ_of_nat /int_np; aw; Ytac0. Qed.

Lemma BZopp_m x: BZopp (BZm_of_nat x) =  BZ_of_nat x.
Proof.
rewrite /BZm_of_nat; Ytac bz; first by rewrite BZopp_0 bz.
by rewrite /BZopp/int_np; aw; Ytac0.
Qed.

Lemma BZopp_m1: BZopp \1mz = \1z.
Proof.  by rewrite /BZ_mone  BZopp_m. Qed.


Lemma BZopp_1: BZopp \1z = \1mz.
Proof.  by rewrite /BZ_one  BZopp_p. Qed.

(** ** Absolute value *)

(** Absolute value is the number with a positive sign; 
   and same numeric value  *)

Definition BZabs x := BZ_of_nat (BZ_val x).

Lemma BZabs_pos x: inc x BZp -> BZabs x = x.
Proof.  apply:BZp_hi_pr. Qed.

Lemma BZabs_neg x: inc x BZms -> BZabs x = BZopp x.
Proof. by move => xz; rewrite /BZabs /BZopp /int_np  (BZms_sg xz); Ytac0. Qed.

Lemma BZabs_m1: BZabs \1mz = \1z.
Proof. by rewrite (BZabs_neg ZmsS_m1) BZopp_m1. Qed.

Lemma BZabs_1: BZabs \1z = \1z.
Proof. exact (BZabs_pos(BZps_sBZp ZpsS1)). Qed.

Lemma BZabs_iN x: intp x -> inc (BZabs x) BZp.
Proof. by move => h; apply: BZ_of_natp_i; apply: BZ_valN. Qed. 

Lemma ZSa x: intp x -> intp (BZabs x).
Proof. move => /BZabs_iN; apply:BZp_sBZ. Qed.

Lemma BZabs_val x: BZ_val (BZabs x) = BZ_val x.
Proof. by  rewrite /BZabs /BZ_of_nat; aw. Qed.

Lemma BZabs_sg x: intp x -> int_pp (BZabs x).
Proof. by rewrite /BZabs /BZ_of_nat /int_pp; aw. Qed.

Lemma BZabs_abs x: BZabs (BZabs x) = BZabs x.
Proof.  by rewrite /BZabs BZabs_val. Qed.
 
Lemma BZabs_opp x:  BZabs (BZopp x) = BZabs x.
Proof. by rewrite /BZabs BZopp_val. Qed.

Lemma BZabs_0 : BZabs \0z = \0z.
Proof. by rewrite /BZabs BZ0_val. Qed.

Lemma BZabs_0p x: inc x BZ -> BZabs x = \0z  -> x = \0z.
Proof. by move => pa /pr1_def /(BZ_0_if_val0 pa).  Qed.


(** ** Orderingssetq1/v     on Z*)

(** We  use the ordinal sum of the opposite ordering of Ns and N.
 This is clearly a total order *)

Definition BZ_order:=
  order_sum2 (opp_order (induced_order Nat_order Nats)) Nat_order.

Lemma BZ_order_aux1: sub Nats (substrate Nat_order).
Proof. by rewrite (proj2 Nat_order_wor) => t /setC1_P []. Qed.

Lemma BZ_order_aux: 
  order (opp_order (induced_order Nat_order Nats))
  /\ order Nat_order.
Proof.  
move: Nat_order_wor => [[or _] _]; move:  BZ_order_aux1 => h.
move: (proj1 (iorder_osr or h)) => h1; move: (proj1 (opp_osr h1)) => h2.
split;fprops.
Qed.

Lemma BZor_or: order BZ_order.
Proof. by  move: BZ_order_aux => [pa pb]; apply: orsum2_or. Qed.

Lemma BZor_sr: substrate BZ_order = BZ.
Proof. 
move: Nat_order_wor => [[or _] sr]; move:  BZ_order_aux1 => s1.
move: (proj1 (iorder_osr or s1)) => h1; move: (opp_osr h1) => [h2 h3].
by rewrite orsum2_sr // h3 sr; rewrite iorder_sr.
Qed.

Lemma BZor_tor: total_order BZ_order.
Proof. 
move:BZ_order_aux1 => h1.
move: (worder_total (proj1 Nat_order_wor)) => h2.
apply:orsum2_totalorder => //.
by apply:total_order_opposite; apply:total_order_sub.
Qed.


Definition BZ_le x y:= [/\ intp x, intp y &
  [\/ [/\ int_np x , int_np y & (BZ_val y) <=c (BZ_val x)],
      [/\ int_np x & int_pp y] |
      [/\ int_pp x, int_pp y &  (BZ_val x) <=c (BZ_val y)]]].
Definition BZ_lt x y:= BZ_le x y /\ x <> y.

Notation "x <=z y" := (BZ_le x y) (at level 60).
Notation "x <z y" := (BZ_lt x y) (at level 60).

(** We define le, lt, ge and gt on Z, and state properties of this operation *)

Lemma zle_P x y: gle BZ_order x y <->  x <=z y.
Proof. 
apply: (iff_trans (orsum2_gleP _ _ x y)).
move: BZ_order_aux => [pa pb].
move: BZor_sr; rewrite orsum2_sr //; move => ->.
split.
  move => [ra rb rc]; split => //; case: rc.
      move => [rd re] /opp_gleP => h; constructor 1;split => //.
      by move: (iorder_gle1 h) => /Nat_order_leP [_ _].
    move => [rd re]  /Nat_order_leP [_ _ rf]; constructor 3;split => //.
     case: (BZ_sgv ra) => //.
    case: (BZ_sgv rb) => //.
  by move => [rd re]; constructor 2;split => //;case: (BZ_sgv rb) => qv.
move => [ra rb rc];split => //. 
move /candu2P: ra => [_ ra]; move /candu2P: rb => [_ rb].
have W := C1_ne_C0; have W' := C0_ne_C1.
case: rc.
    move => [rd re rf]; constructor 1 ;split => //.
    case: ra;  [move => [p1 _] | by move => [_]; rewrite rd].
    case: rb;  [move => [p2 _] | by move => [_]; rewrite re].
    apply /opp_gleP; apply /iorder_gle0P => //. 
    apply /Nat_order_leP; split => //.
      by case /setC1_P: p2. 
    by case /setC1_P: p1.
  by move => [rd re]; constructor 3;split => //; rewrite re.
move => [rd re rf]; constructor 2; rewrite rd re; split => //.
case: ra; [ by move => [_]; rewrite rd | move => [p1 _] ].
case: rb; [ by move => [_]; rewrite re | move => [p2 _] ].
by apply /Nat_order_leP.
Qed.

Lemma zlt_P x y: glt BZ_order x y <-> x <z y.
Proof. by split; move => [ha hb]; split => //; apply/zle_P. Qed.

Lemma zleT a b c:  a <=z b -> b <=z c ->  a <=z c.
Proof. 
move: BZor_or => h /zle_P pa /zle_P pb; apply /zle_P;order_tac.
Qed.

Lemma zleR a: intp a -> a <=z a.
Proof. 
by move: BZor_or => h az;apply /zle_P; order_tac;rewrite BZor_sr.
Qed.

Lemma zleA a b:  a <=z b -> b <=z a -> a = b.
Proof. move: BZor_or => h /zle_P pa /zle_P pb; order_tac. Qed.

Lemma zleNgt a b: a <=z b -> ~(b <z a).
Proof. by move => pa [pb]; case; apply:zleA. Qed.

Lemma zlt_leT a b c: a <z b -> b <=z c -> a <z c.
Proof. 
move => [pa pb] pc;split; first apply: (zleT pa pc).
move => ac; case: pb; apply :zleA => //; ue.
Qed.

Lemma zltNge a b:  a <z b -> ~ b <=z a.
Proof. move => ha hb; exact:(zleNgt hb ha). Qed.

Lemma zle_ltT a b c: a <=z b -> b <z c -> a <z c.
Proof. 
move => pa [pb pc];split; first apply: (zleT pa pb).
move => ac; case: pc;apply :zleA => //; ue.
Qed.


Lemma zle_eqVlt a b :  a <=z b -> a = b \/ a <z b.
Proof.
move => le; case: (equal_or_not a b) => h; [by left |  by right].
Qed.

Ltac BZo_tac := match goal with
  | Ha: ?a <=z ?b, Hb: ?b <=z ?c |-  ?a <=z ?c  
     =>  apply: (zleT Ha Hb)
  | Ha: ?a <z  ?b, Hb: ?b <=z ?c |-  ?a <z ?c  
     =>  apply: (zlt_leT Ha Hb)
  | Ha:?a <=z ?b, Hb: ?b <z ?c |-  ?a <z ?c  
     =>  apply: (zle_ltT Ha Hb)
  | Ha: ?a <z ?b, Hb: ?b <z ?c |-  ?a <z ?c  
     => apply: (zle_ltT (proj1 Ha) Hb)
  | Ha: ?a <=z ?b, Hb: ?b <z ?a |- _ 
    => case: (zleNgt Ha Hb)
  | Ha: ?x <=z  ?y, Hb: ?y  <=z ?x |- _ 
   => solve [ rewrite (zleA Ha Hb) ; fprops ]
  | Ha: intp ?x  |- ?x <=z ?x  => apply: (zleR Ha)
  | Ha: ?a  <=z  _ |- intp ?a =>  exact (proj31 Ha)
  | Ha:  _ <=z ?a |- intp ?a =>  exact (proj32 Ha)
  | Ha:  ?a <z _ |- intp ?a => exact (proj31_1 Ha) 
  | Ha:  _ <z ?a |- intp ?a => exact (proj32_1 Ha) 
  | Ha: ?a <z ?b  |-  ?a <=c ?b => by move: Ha => []
end.

Lemma zleT_ee a b: intp a -> intp b -> a <=z b  \/ b <=z a.
Proof.
move: BZor_tor => [_]; rewrite BZor_sr => h pa pb.
by case: (h _ _ pa pb)=> h1; [left | right]; apply /zle_P.
Qed.

Lemma zleT_ell a b:  intp a -> intp b -> [\/ a = b, a <z b | b <z a].
Proof.
move => pa pb; case: (equal_or_not a b); first by constructor 1.
by move => na; case: (zleT_ee pa pb)=> h1; [constructor 2 | constructor 3];
   split => //; apply: nesym.
Qed.

Lemma zleT_el a b:  intp a -> intp b->  a <=z b  \/ b <z a.
Proof. 
move=> ca cb; case: (zleT_ell ca cb).
- move=> ->; left. BZo_tac.
- by move => [pa _]; left.
- by right.
Qed.

Lemma zle_P1 x y: inc x BZp ->  inc y BZp -> 
  (x <=z y <-> (BZ_val x) <=c (BZ_val y)).
Proof. 
move => pa pb; move: (BZp_sg pa) (BZp_sg pb) => pc pd.
move:(BZp_sBZ pa) (BZp_sBZ pb) => pa' pb'.
split.
  move=> [_ _]; rewrite /int_np pc; by case; move => [ba] => //; case:C0_ne_C1.
by move => h; split => //; constructor 3.
Qed.

Lemma zle_pr2 x y: inc x BZp -> inc y BZms ->  y <z x.
Proof. 
move => pa pb; move:(BZp_sg pa) (BZms_sg pb) => pc pd.
move:(BZp_sBZ pa) (BZms_sBZ pb) => pa' pb'.
split; first by split => //; constructor 2.
move /(congr1 Q); rewrite pc pd; fprops.
Qed.

Lemma zle_P3 x y: inc x BZms -> inc y BZms ->
  (x <=z y <-> (BZ_val y) <=c (BZ_val x)).
Proof. 
move => pa pb; move: (BZms_sg pa) (BZms_sg pb) => pc pd.
move:(BZms_sBZ pa) (BZms_sBZ pb) => pa' pb'.
split.
  by move => [_ _]; rewrite/int_pp pd; case =>  [][aa bb] //;  case:C0_ne_C1.
by move=> h; split => //; constructor 1. 
Qed.

Lemma zle_pr4 x y: inc x BZp -> inc y BZms -> ~ (x <=z y).
Proof.  move => pa pb; move: (zle_pr2 pa pb) => pc pd; BZo_tac. Qed.

Lemma zle_P0 x y:
   x <=z y <->  
   [\/ [/\ inc x BZms, inc y BZms & (BZ_val y) <=c (BZ_val x)],
       [/\ inc x BZms & inc y BZp] |
       [/\ inc x BZp, inc y BZp &  (BZ_val x) <=c (BZ_val y)]].
Proof. 
split.
  move => h; move:(h) => [pa pb _].
  case /BZ_i0P: pa => ha; case /BZ_i0P: pb => hb.
  by constructor 1 ;split => //; move /(zle_P3 ha hb): h.
  by constructor 2; split => //.
  by move: (zle_pr4 ha hb) => hc.
  by constructor 3;split => //;  move /(zle_P1 ha hb): h.
case; first by move => [pa pb pc]; apply /zle_P3.
  by  move => [pa pb]; exact: (proj1 (zle_pr2 pb pa)).
by move => [pa pb pc]; apply /zle_P1.
Qed.

Lemma zle_pr5 x y: inc x BZp ->  inc y BZp -> 
  (x <=z y =  (BZabs x) <=z (BZabs y)).
Proof. move => pa pb; rewrite !BZabs_pos //. Qed.

Lemma zlt_P1 x y: inc x BZp ->  inc y BZp -> 
  (x <z y <->  (BZ_val x) <c (BZ_val y)).
Proof. 
move => pa pb; split; move => [pc pd]; split.
+ by apply/(zle_P1 pa pb).
+ by dneg h; rewrite - (BZp_hi_pr pa) - (BZp_hi_pr pb) h.
+ by apply /(zle_P1 pa pb).
+ by dneg h; rewrite h.
Qed.

Lemma zle_cN a b: natp a -> natp b ->
    (a <=c b <-> BZ_of_nat a <=z BZ_of_nat b).
Proof.
move => aN bN;apply: iff_sym.
by move:(zle_P1 (BZ_of_natp_i aN)(BZ_of_natp_i bN)); rewrite !BZ_of_nat_val.
Qed.

Lemma zlt_cN a b: natp a -> natp b ->
    (a <c b <-> BZ_of_nat a <z BZ_of_nat b).
Proof.
move => aN bN;apply: iff_sym.
by move:(zlt_P1 (BZ_of_natp_i aN)(BZ_of_natp_i bN)); rewrite !BZ_of_nat_val.
Qed.

Lemma zlt_24: \2z <z \4z.
Proof. by move /(zlt_cN NS2 NS4):clt_24. Qed.

Lemma zle_24: \2z <=z \4z.
Proof. exact (proj1 zlt_24). Qed. 

Lemma zle0xP x: \0z <=z x <-> inc x BZp.
Proof. 
split.
  move => [pa pb pc]; case /BZ_i0P: pb => // xn.
  have h: int_np \0z -> False by  rewrite /int_np  BZ0_sg; fprops.
  case: pc; case => // _.
  by move: (BZms_sg xn); rewrite /int_pp /int_np => -> /C0_ne_C1.
move => xp. move:(BZp_sBZ xp) ZS0 => xz z0; split => //; constructor 3.
split; [ exact BZ0_sg |  exact: (BZp_sg xp) | ].
by move: (BZ_valN (BZp_sBZ xp)) =>/cle0n; rewrite BZ0_val. 
Qed.
 
Lemma zlt0xP x: \0z <z x <-> inc x BZps.
Proof.
split.
   by move => [/zle0xP pa /nesym pb]; apply /BZps_iP.
by move /BZps_iP => [pa pb]; split; [apply /zle0xP |apply: nesym].
Qed.

Lemma zgt0xP x: x <z \0z <->  inc x BZms.
Proof. 
split.
  move => pa; case /BZ_i0P: (proj31_1 pa) => //.
  move /zle0xP => h; BZo_tac.
move => h; move: (zleT_el ZS0 (BZms_sBZ h)); case => //.
move /zle0xP => h1;case:(BZ_di_neg_pos h h1).
Qed.

Lemma zge0xP x: x <=z \0z <-> inc x BZm.
Proof. 
split.
   move => h; apply /setU1_P;case: (equal_or_not x \0z) => xnz; first by right.
   by left; apply /zgt0xP; split.
case /setU1_P; first by case /zgt0xP.
move => ->;move: ZS0 => h; BZo_tac.
Qed.

Lemma zle_P6 x y: inc x BZm -> inc y BZm ->
  (x <=z y <->  (BZ_val y) <=c (BZ_val x)).
Proof.
case /setU1_P => xnz; case /setU1_P => ynz.
- apply /(zle_P3 xnz ynz).
- rewrite ynz BZ0_val; split. 
    move => _;  move: (BZ_valN (BZms_sBZ xnz)) => /cle0n xn //.
    by move /zgt0xP: xnz => [pa _ ].
- rewrite xnz; split.
    by move/zle0xP => h; case:(BZ_di_neg_pos ynz h).
  rewrite  BZ0_val => pc; move /indexed_P: ynz => [_] /setC1_P [pa pb] _.
  case: pb; exact (cle0 pc).
- rewrite xnz ynz BZ0_val;move :ZS0 =>h; split=> _; fprops; BZo_tac.
Qed.

Lemma BZabs_positive b: intp b -> b <> \0z -> \0z <z (BZabs b).
Proof. 
move => pa pb; apply /zlt0xP. 
apply /BZps_iP;split; first by apply BZabs_iN.
by move => h; case: pb; apply:BZabs_0p. 
Qed. 


(** Opposite is an order isomorphism from (Z,<) to (Z,>) *)

Lemma zle_opp x y: x <=z y ->  (BZopp y) <=z  (BZopp x).
Proof.
move => leq; move: (leq) => [xz yz etc].
case: (equal_or_not x \0z) => xnz.
   move: leq; rewrite xnz => /zle0xP yp; rewrite BZopp_0.
   by apply/zge0xP; apply: BZopp_positive2.
case: (equal_or_not y \0z) => ynz.
   move: leq; rewrite ynz => /zge0xP yp;rewrite BZopp_0.
   by apply/zle0xP; apply: BZopp_negative2.
move: (ZSo xz) (ZSo yz) => x'z y'z.
split => //; rewrite  (BZopp_val x)  (BZopp_val y).
move: (BZopp_sg xz xnz) (BZopp_sg yz ynz) => [qa qb][qc qd].
case: etc.
- move => [pa pb pc]; constructor 3; split; fprops. 
- move => [pa pb];constructor 2; split; fprops.
- by move => [pa pb pc]; constructor 1; split; fprops.  
Qed.


Lemma zlt_opp x y: x <z y -> (BZopp y) <z (BZopp x).
Proof. 
move => [pa pb]; split; first by apply:zle_opp.
by move: pa => [xz yz _] pc; case: pb; apply:BZopp_inj.
Qed.

Lemma zle_oppP x y: intp x -> intp y ->
  (BZopp y <=z BZopp x <-> x <=z y).
Proof. 
move => pa pb; split; last by apply: zle_opp.
by move=> h; move: (zle_opp h); rewrite (BZopp_K pa) (BZopp_K pb).
Qed.

Lemma zlt_oppP x y: intp x -> intp y ->
  (BZopp y <z BZopp x <-> x <z y).
Proof. 
move => pa pb; split; last by apply: zlt_opp.
by move=> h; move: (zlt_opp h); rewrite (BZopp_K pa) (BZopp_K pb).
Qed.

Lemma zle_opp_iso:
  order_isomorphism (Lf BZopp BZ BZ) BZ_order (opp_order BZ_order).
Proof. 
move: BZor_or BZor_sr BZopp_fb => or sr bf.
have la: lf_axiom BZopp BZ BZ by move => t /ZSo.
move: (opp_osr or) => [pa pb].
hnf;rewrite pb /BZopp_fun; aw;split; [exact | fprops | split; aw=> // | ].
hnf; aw;move => x y xz yz; rewrite !LfV //; split.
  by move /zle_P => h; apply /opp_gleP; apply /zle_P;apply zle_opp.
by move /opp_gleP /zle_P /(zle_oppP xz yz) /zle_P. 
Qed.


(** ** Addition *)

Definition BZsum_v1 x y :=
  let f := fun x => Yo (inc x BZp) (J \0c (BZ_val x)) (J (BZ_val x) \0c) in
  let g := fun x => Yo ((P x) <=c (Q x))
                       (BZ_of_nat((Q x) -c (P x))) (BZm_of_nat ((P x) -c (Q x))) in
  let h := fun x y => J ( (P x) +c (P y)) ( (Q x) +c (Q y)) in
  g (h (f x) (f y)).

  
Definition BZsum_v2 x y:=
  let abs_sum :=  (BZ_val x) +c (BZ_val y) in
    let abs_diff1 :=  (BZ_val x) -c (BZ_val y) in
      let abs_diff2 :=  (BZ_val y) -c (BZ_val x) in
        Yo (inc x BZp /\ inc y BZp) (BZ_of_nat abs_sum)
        (Yo ( ~ inc x BZp /\ ~ inc y BZp) (BZm_of_nat abs_sum)
          (Yo (inc x BZp /\ ~ inc y BZp) 
            (Yo ( (BZ_val y) <=c (BZ_val x)) 
              (BZ_of_nat abs_diff1) (BZm_of_nat abs_diff2))
            (Yo ( (BZ_val x) <=c (BZ_val y)) 
              (BZ_of_nat abs_diff2) (BZm_of_nat abs_diff1)))).

Definition BZsum := locked BZsum_v2.
Notation "x +z y" := (BZsum x y) (at level 50).

Lemma csubn0 x: cardinalp x -> x -c \0c = x.
Proof. by move => /card_card => {2} <-; rewrite /cdiff setC_0. Qed.

Lemma BZsum_spec x: cardinalp x ->
 Yo (x <=c \0c) (BZ_of_nat (\0c -c x)) (BZm_of_nat (x -c \0c)) = BZm_of_nat x.
Proof.
move => h.
case: (p_or_not_p (x <=c \0c)) => ww; Ytac0.
  by rewrite (cle0 ww) (csubn0 CS0) // /BZm_of_nat; Ytac0.
by rewrite csubn0.
Qed.

  
Lemma BZsum_alt x y: intp x -> intp y -> BZsum_v2 x y = BZsum_v1 x y.
Proof.
have Hb := CS_sum2 (P x) (P y).
rewrite /BZsum_v1 /BZsum_v2 pr1_pair pr2_pair => xz yz.
move: (BZ_valN xz) (BZ_valN yz) => pxn pyn.
case: (p_or_not_p (inc x BZp));case: (p_or_not_p (inc y BZp)) => hx hy.
- have hxy: (inc x BZp /\ inc y BZp) by [].
  have sp: \0c <=c (P x +c P y) by apply: cle0x.
  Ytac0; Ytac0; Ytac0; rewrite !pr1_pair !pr2_pair (csum0l CS0); Ytac0.
  by rewrite (csubn0 Hb).
- have hxy: ~ (inc x BZp /\ inc y BZp) by case.
  have hxy2: ~(~ inc x BZp /\ ~ inc y BZp) by case.
  have hxy3: (inc x BZp /\ ~ inc y BZp) by split.
  Ytac0; Ytac0; Ytac0; Ytac0; Ytac0; rewrite !pr1_pair !pr2_pair.
  by rewrite (Nsum0l pyn) (Nsum0r pxn).
- have hxy: ~ (inc x BZp /\ inc y BZp) by case.
  have hxy2: ~(~ inc x BZp /\ ~ inc y BZp) by case.
  have hxy3: ~(inc x BZp /\ ~ inc y BZp) by case.
  Ytac0; Ytac0; Ytac0; Ytac0; rewrite !pr1_pair !pr2_pair.
  by Ytac0; rewrite pr1_pair pr2_pair (Nsum0l pyn) (Nsum0r pxn).
- have hxy: ~(inc x BZp /\ inc y BZp) by case.
  have hxy2: (~ inc x BZp /\ ~ inc y BZp) by split.
  Ytac0; Ytac0; Ytac0; Ytac0; rewrite !pr1_pair !pr2_pair (csum0l CS0).
  by rewrite (BZsum_spec Hb).
Qed.

Lemma BZsumE x y :  x +z y = BZsum_v2 x y.
Proof. by rewrite /BZsum - lock.  Qed. 
  
Lemma BZsumC x y:  x +z y = y +z x.
Proof.
rewrite /BZsum - lock /BZsum_v2.
case:(p_or_not_p (inc x BZp)) => hx;case:(p_or_not_p (inc y BZp)) => hy.
- by rewrite (Y_true (conj hx hy)) (Y_true (conj hy hx)) csumC.
- have ha: ~(inc x BZp /\ inc y BZp)  by case.
  have hb: ~(inc y BZp /\ inc x BZp) by case.
  have hc: ~(~ inc x BZp /\ ~ inc y BZp) by case.
  have hd: ~(~ inc y BZp /\ ~ inc x BZp) by case.
  have he:~(inc y BZp /\ ~ inc x BZp) by case.
  by Ytac0; Ytac0; Ytac0; Ytac0; Ytac0; rewrite (Y_true (conj hx hy)).
- have ha: ~(inc x BZp /\ inc y BZp)  by case. 
  have hb: ~(inc y BZp /\ inc x BZp) by case. 
  have hc: ~(~ inc x BZp /\ ~ inc y BZp) by case.
  have hd: ~(~ inc y BZp /\ ~ inc x BZp) by case.
  have he:~(inc x BZp /\ ~ inc y BZp) by case.
  by Ytac0; Ytac0; Ytac0; Ytac0; Ytac0; rewrite (Y_true (conj hy hx)).
- have ha: ~(inc x BZp /\ inc y BZp) by case.
  have hb: ~(inc y BZp /\ inc x BZp) by case. 
  by Ytac0;Ytac0; rewrite (Y_true (conj hx hy)) (Y_true (conj hy hx)) csumC.
Qed.


Lemma BZsum_pp x y: inc x BZp -> inc y BZp ->
  x +z y = BZ_of_nat ((BZ_val x) +c (BZ_val y)).
Proof. 
have Hb := CS_sum2 (P x) (P y).
move: CS0 => cs0 xp yp. 
by rewrite BZsumE /BZsum_v2 !Y_true; aw; fprops;rewrite csubn0.
Qed.

Lemma BZsum_mm x y: inc x BZms -> inc y BZms ->
  x +z y = BZm_of_nat ((BZ_val x) +c (BZ_val y)).
Proof. 
move => xm ym.
have pa: (~ inc x BZp) by move => pa; case: (BZ_di_neg_pos xm pa).
have pb: (~ inc y BZp) by move => pb; case: (BZ_di_neg_pos ym pb).
have pc: ~ (inc x BZp /\ inc y BZp) by case.
by rewrite BZsumE /BZsum_v2 (Y_false pc) (Y_true (conj pa pb)). 
Qed.

Lemma BZsum_pm x y: inc x BZp -> inc y BZms ->
  x +z y = (Yo ((BZ_val y) <=c (BZ_val x)) 
    (BZ_of_nat ((BZ_val x) -c (BZ_val y)))
    (BZm_of_nat ((BZ_val y) -c (BZ_val x)))).
Proof. 
move => xp ym.
rewrite BZsumE /BZsum_v2.
have pb: (~ inc y BZp) by move => pb; case: (BZ_di_neg_pos ym pb).
have pa: ~ (inc x BZp /\ inc y BZp) by case.
have pc: ~ (~ inc x BZp /\ ~ inc y BZp) by case.
by rewrite (Y_false pa) (Y_false pc) (Y_true (conj xp pb)).
Qed.

Lemma BZsum_pm1 x y: inc x BZp -> inc y BZms ->
  (BZ_val y) <=c (BZ_val x) -> x +z y = BZ_of_nat((BZ_val x) -c (BZ_val y)).
Proof. by  move => pa pb pc; rewrite BZsum_pm //; Ytac0. Qed. 

Lemma BZsum_pm2 x y: inc x BZp -> inc y BZms ->
  (BZ_val x) <c (BZ_val y) -> x +z y = (BZm_of_nat ((BZ_val y) -c (BZ_val x))).
Proof. 
move => pa pb pc; rewrite BZsum_pm // Y_false //.
move => h;apply: (cleNgt h pc).
Qed.

Lemma ZSs x y: intp x -> intp y -> intp (x +z y).
Proof. 
move => xz yz; rewrite  BZsumE /BZsum_v2.
move: (BZ_valN xz)(BZ_valN yz) => pxn qxn.
Ytac h1; first by apply:BZ_of_nat_i; apply:NS_sum.
Ytac h2; first by apply:BZm_of_nat_i; apply:NS_sum.
Ytac h3. 
   by Ytac h4; [apply:BZ_of_nat_i | apply:BZm_of_nat_i]; apply: NS_diff.
by Ytac h4; [apply:BZ_of_nat_i | apply:BZm_of_nat_i ];apply: NS_diff.
Qed.

Lemma BZsum_cN x y: natp x  ->  natp y  -> 
  BZ_of_nat x +z BZ_of_nat y = BZ_of_nat (x +c y).
Proof.
move => xN yN; rewrite (BZsum_pp (BZ_of_natp_i xN) (BZ_of_natp_i yN)).
by rewrite !BZ_of_nat_val.
Qed.


Lemma BZsum_0l x: intp x -> \0z +z x  = x.
Proof.
move => xz; rewrite BZsumE /BZsum_v2. 
have cp:= (CS_nat (BZ_valN xz)).
case: (p_or_not_p (inc x BZp)) => hx.
  rewrite (Y_true (conj ZpS0 hx)) /BZ_zero /BZ_of_nat; aw; rewrite csum0l//.
  exact:(BZp_hi_pr hx).
have ha:= ZpS0.
have hb: ~(inc \0z BZp /\ inc x BZp) by case.
have hc: ~ (~ inc \0z BZp /\ ~ inc x BZp) by case.
have hd: (inc \0z BZp /\ ~ inc x BZp)  by  split.
Ytac0; Ytac0; Ytac0; rewrite /BZ_zero /BZ_of_nat; aww.
rewrite (BZsum_spec cp) BZm_hi_pr //. 
by case/BZ_i0P: xz => // /BZms_sBZm.
Qed.

Lemma BZsum_0r x: intp x -> x +z \0z = x.
Proof. by move => xz;rewrite BZsumC BZsum_0l. Qed.

Lemma BZsum_11 : \1z +z \1z = \2z. 
Proof.
have ha := (BZps_sBZp ZpsS1).
by rewrite BZsum_pp // /BZ_one/BZ_of_nat !pr1_pair csum_11.
Qed.

Lemma BZsum_opp_r x: intp x -> x +z (BZopp x) = \0z.
Proof. 
move => xz.
wlog: x xz / inc x BZps.
  move => H;case /BZ_i1P: (xz). 
  + by move => ->; rewrite BZopp_0 BZsum_0l //; apply: ZS0.
  + by apply: H.
  + move => xm; move: (BZopp_negative1 xm) => xm1.
    rewrite BZsumC - {2} (BZopp_K (BZms_sBZ xm));exact: (H _ (ZSo xz) xm1).
move =>  yp; move: (BZopp_positive1 yp) => yp1.
move: (BZps_sBZp yp) => yp2.
case: (inc_or_not (BZopp x) BZp) => h1; first by case: (BZ_di_neg_pos yp1 h1).
have ha: ~(inc x BZp /\ inc (BZopp x) BZp) by case.
have hb: ~(~ inc x BZp /\ ~ inc (BZopp x) BZp) by case.
rewrite BZsumE /BZsum_v2 (Y_false ha) (Y_false hb) (Y_true (conj yp2 h1)).
by rewrite BZopp_val (Y_true (cleR (CS_nat (BZ_valN xz)))) cdiff_nn.
Qed.

Lemma BZsum_opp_l x: intp x -> (BZopp x) +z x = \0z.
Proof. by move => h; rewrite BZsumC BZsum_opp_r. Qed.

Lemma BZoppD x y: intp x -> intp y ->
  BZopp (x +z y) = (BZopp x) +z (BZopp y).
Proof. 
pose R a b := BZopp (a +z b) = BZopp a +z BZopp b.
have ha :forall a b, inc a BZps -> inc b BZms -> R a b.
  move => a b ap bn; rewrite /R.
  move: (BZps_sBZp ap) => ap1.
  rewrite (BZsum_pm ap1 bn).
  move: (BZ_valN (BZps_sBZ ap)) (BZ_valN (BZms_sBZ bn)) => pa pb.
  case: (equal_or_not (P a) (P b)) => pab.
    have hb: (BZopp b = a).
      by rewrite /BZopp /int_np -pab (BZms_sg bn); Ytac0; apply BZp_hi_pr.
    rewrite hb (BZsum_opp_l (BZps_sBZ ap)).
    rewrite Y_true pab; [ by rewrite cdiff_nn -/BZ_zero BZopp_0| fprops].
  move: (BZopp_positive1 ap) (BZopp_negative1 bn) => nab nbc.
  rewrite BZsumC  (BZsum_pm (BZps_sBZp nbc) nab) ! BZopp_val.
  case: (cleT_ee (CS_nat pb)  (CS_nat pa)) => h.
    have h1: ~(P a <=c P b) by move => /(cleA h) ee; case: pab.
    by Ytac0; Ytac0; rewrite /BZ_of_nat /BZopp/int_np; aw; Ytac0.
  have h1: ~(P b <=c P a) by move => /(cleA h) ee; case: pab. 
  move: (cdiff_nz (conj h pab)) => h2.
  by rewrite /BZopp /BZm_of_nat/int_np; Ytac0; Ytac0; Ytac0;aw; Ytac0; Ytac0.
have hb :forall a b, inc a BZps -> inc b BZps -> R a b.
  move => a b pa pb. 
  move: (BZopp_positive1 pa) (BZopp_positive1 pb) => n1 n2.
  move:(BZps_sBZp pa)(BZps_sBZp pb) => pa' pb'.
  rewrite /R BZsum_pp //  BZsum_mm // ! BZopp_val.
  by rewrite /BZopp /BZ_of_nat/int_np; aw; Ytac0.
have hc :forall a b, inc a BZps -> inc b BZ -> R a b.
  move => a b az bz; case /BZ_i1P: bz.
  + move: (BZps_sBZ az) => az1; move:(ZSo az1) => az2.
    move => ->; rewrite /R  BZopp_0 !BZsum_0r //. 
  + by move=> bz; apply: hb.
  + by move=> bz;apply: ha.
move => xz yz; case /BZ_i1P: (xz) => xs.
+ by move:(ZSo yz) => yz2; rewrite xs /R  BZopp_0 !BZsum_0l.
+ by apply: hc.
+ symmetry;rewrite - {2} (BZopp_K yz) - {2} (BZopp_K xz).
  move: (BZopp_negative1 xs)  (ZSo xz) (ZSo yz) => xz1 xz2 yz1.
  by rewrite - (hc _ _ xz1 yz1) BZopp_K //; apply: ZSs.
Qed.

Lemma BZsum_N_Ns x y: natp x -> inc y Nats ->  inc (x +c y) Nats.
Proof. 
move => xb /setC1_P [yn yz]; apply /setC1_P;split; first by apply: NS_sum.
move: (cpred_pr yn yz) => [pa pb].
rewrite pb (csum_nS _ pa);apply: succ_nz.
Qed.

Lemma ZpS_sum x y: inc x BZp -> inc y BZp -> inc (x +z y) BZp.
Proof. 
move => pa pb; rewrite (BZsum_pp pa pb); apply BZ_of_natp_i.
move: (BZ_valN (BZp_sBZ pa)) (BZ_valN (BZp_sBZ pb)) => sa sb.
by apply:NS_sum.
Qed.

Lemma ZpsS_sum_r x y: inc x BZp -> inc y BZps -> inc (x +z y) BZps.
Proof. 
move => pa pb.
move: (pa) (pb) => /indexed_P [_ q1 _] /indexed_P [_ q2 _]. 
move /BZps_iP: pb => [pb pc];rewrite (BZsum_pp pa pb); apply /indexed_pi.
apply: (BZsum_N_Ns q1 q2).
Qed.

Lemma ZpsS_sum_l x y: inc x BZps -> inc y BZp ->  inc (x +z y) BZps.
Proof. by move => pa pb; rewrite BZsumC; apply ZpsS_sum_r.  Qed.

Lemma ZpsS_sum_rl x y: inc x BZps -> inc y BZps -> inc (x +z y) BZps.
Proof. by move => pa pb; apply: ZpsS_sum_r => //;apply:BZps_sBZp. Qed.

Lemma ZmsS_sum_rl x y: inc x BZms -> inc y BZms -> inc (x +z y) BZms.
Proof.
move => xz yz.
move: (BZopp_negative1 xz) (BZopp_negative1 yz) => xz1 yz1.
move: (BZms_sBZ xz)(BZms_sBZ yz) => xz2 yz2.
move: (ZpsS_sum_rl xz1 yz1); rewrite - (BZoppD xz2 yz2) => h.
by move: (BZopp_K (ZSs xz2 yz2)) => <-; apply: BZopp_positive1.
Qed.

Lemma ZmsS_sum_r x y: inc x BZm -> inc y BZms ->  inc (x +z y) BZms.
Proof. 
case /setU1_P; first by apply:ZmsS_sum_rl.
by move => -> h; rewrite BZsum_0l //; apply: BZms_sBZ.
Qed.

Lemma ZmsS_sum_l x y: inc x BZms -> inc y BZm -> inc (x +z y) BZms.
Proof. by  move => pa pb;rewrite BZsumC; apply: ZmsS_sum_r. Qed.

Lemma ZmS_sum x y: inc x BZm -> inc y BZm -> inc (x +z y) BZm.
Proof. 
case /setU1_P; first by move => pa pb; apply:BZms_sBZm; apply:ZmsS_sum_l.
by move => -> h; rewrite BZsum_0l //;  apply: BZm_sBZ.
Qed.
 
Lemma BZsumA x y z: intp x -> intp y -> intp z ->
  x +z (y +z z) = (x +z y) +z z.
Proof. 
move: x y z.
pose f x := Yo (inc x BZp) (J \0c (P x)) (J (P x) \0c).
pose g x := Yo ((P x) <=c (Q x))
    (BZ_of_nat((Q x) -c (P x))) (BZm_of_nat ((P x) -c (Q x))).
have Ha: forall x, inc x BZ -> g (f x) = x. 
   move => x xz; rewrite /f/g; case: (inc_or_not x BZp) => h1; Ytac0; aw.
     move: (BZ_valN xz) => pa; move: (cle0n pa) => h2; Ytac0.
     by rewrite (cdiff_n0 pa); apply: BZp_hi_pr.
   case /BZ_i0P: xz => zt; last by [].
   move /indexed_P: (zt) => [_] /setC1_P [pa pb] _.
   have hh: ~(P x <=c \0c). 
     by move => /cle0.
   by Ytac0 ;rewrite (cdiff_n0 pa); apply: BZm_hi_pr;apply:BZms_sBZm.
set (NN:= Nat \times Nat).
pose h x y := J ( (P x) +c (P y)) ( (Q x) +c (Q y)).
have Hu: forall x y, inc x NN -> inc y NN
    -> ((g x = g y) <-> ( (P x) +c (Q y) =  (P y) +c (Q x))).
  move => x y /setX_P [_ pa pb] /setX_P [_ pc pd]; rewrite /g.
  case:(cleT_el (CS_nat pa)(CS_nat pb)) => h1;
     case:(cleT_el (CS_nat pc)(CS_nat pd)) => h2.
  - Ytac0; Ytac0; move: (cdiff_pr h1) (cdiff_pr h2).
    set a:= Q x -c P x; set b:=  Q y -c P y; move => eqa eqb.
    rewrite /BZ_of_nat; split => ha.
      by rewrite - eqa -eqb (pr1_def ha) csumA (csumA (P y)) (csumC (P y)).
    congr (J _ C1); move: ha; rewrite -eqa csumA - eqb csumA (csumC (P x)).
    move => t; symmetry;apply:(csum_eq2l (NS_sum pc pa) _ _ t);
    rewrite /a /b; fprops.
  - have  h3:=(cltNge h2).
    move: (cdiff_nz h2) => h4.
    Ytac0; Ytac0; rewrite /BZ_of_nat /BZm_of_nat; Ytac0; split => h5.
      by case: C1_ne_C0; move: (pr2_def h5).
    by move: (csum_Mlelt pb h1 h2); rewrite h5 csumC; move => [_].
  - have  h3:=(cltNge h1).
    move: (cdiff_nz h1) => h4.
    Ytac0; Ytac0; rewrite /BZ_of_nat /BZm_of_nat; Ytac0; split => h5.
      by case: C1_ne_C0; move: (pr2_def h5).
    by move: (csum_Mlelt pd h2 h1); rewrite - h5 csumC; move => [_].
  - have  h3:=(cltNge h1). 
    have  h4:=(cltNge h2).
    move: (cdiff_nz h2) => h5.
    move: (cdiff_nz h1) => h6.
    Ytac0; Ytac0; rewrite /BZm_of_nat; Ytac0; Ytac0.
    move: (cdiff_pr(proj1 h1)) (cdiff_pr (proj1 h2)).
    set a:= P x -c Q x; set b:=  P y -c Q y; move => eqa eqb.
    split => ha.
      by rewrite - eqa -eqb (pr1_def ha) - csumA csumC  (csumC b).
    congr (J _ C0); move: ha; rewrite -eqa csumC  csumA - eqb.
    rewrite (csumC _ b) - (csumA b) (csumC (Q y)) (csumC b) => t.
    apply:(csum_eq2l (NS_sum pb pd) _ _ t); rewrite /a /b; fprops.
have H: (forall x y, intp x -> intp y -> x +z y = g (h (f x) (f y))).
   by move => x y xi yi; rewrite BZsumE BZsum_alt.
have Hf:forall x, inc x BZ -> inc (f x) NN.
  move => x xz; move: (BZ_valN xz) => pb.
  rewrite /f; Ytac t; apply: setXp_i => //; apply: NS0.
have Hg:forall x, inc x NN -> inc (g x) BZ. 
  move => x /setX_P [_ pa pb]; rewrite /g; Ytac aux.
    by apply: BZ_of_nat_i; apply:NS_diff.
    by apply: BZm_of_nat_i; apply:NS_diff.
have Hh:forall u v, inc u NN -> inc v NN -> inc (h u v) NN.
  move => u v /setX_P [_ pa pb] /setX_P [_ pc pd]. 
  by apply: setXp_i; apply: NS_sum.
move => x y z xZ yZ zZ; move: (ZSs xZ yZ) (ZSs yZ zZ).
set (yz:=  y +z z); set (xy:= x +z y) => xyZ yzZ.
have : (g (f yz) = g (h (f y) (f z))) by rewrite Ha // /yz - (H _ _ yZ zZ).
move /(Hu _ _ (Hf _ yzZ) (Hh _ _ (Hf _ yZ) (Hf _ zZ))) => eq1.
have:  (g (f xy) = g (h (f x) (f y))) by rewrite Ha // /xy - (H _ _ xZ yZ).
move /(Hu _ _ (Hf _ xyZ) (Hh _ _ (Hf _ xZ) (Hf _ yZ))) => eq2. 
rewrite (H _ _ xZ yzZ) (H _ _ xyZ zZ).
apply /(Hu _ _ (Hh _ _ (Hf _ xZ) (Hf _ yzZ)) (Hh _ _ (Hf _ xyZ) (Hf _ zZ))). 
move: eq1 eq2;rewrite /h !pr1_pair !pr2_pair.
move: (Hf _ xZ) => /setX_P [_].
move: (Hf _ yZ) => /setX_P [_ ].
move: (Hf _ zZ) => /setX_P [_].
move: (Hf _ xyZ) => /setX_P [_ ].
move: (Hf _ yzZ) => /setX_P [_].
set (Px:= P (f x)); set (Qx:=Q (f x)); set (Py:= P (f y)); set (Qy:=Q (f y)).  
set (Pz:= P (f z)); set (Qz:=Q (f z)); set (Pyz:= P (f yz)). 
set (Qyz:= Q (f yz)) ; set (Pxy:= P (f xy)); set (Qxy:= Q (f xy)).
move => pyzb qyzb pxyb qxyb pzb qzb pyb qyb pxb qxb eq1 eq2.
apply: (csum_eq2r qyb); [ fprops | fprops |].
rewrite - csumA - csumA.
set a := Pyz +c _.
have -> : a = (Pyz +c (Qy +c Qz)) +c Qxy.
  rewrite /a - (csumA _ _ Qxy); congr (Pyz +c _).
  by rewrite csumC (csumC Qxy) csumA. 
set b := _ +c Qy.
have -> :  b = ((Pxy +c (Qx +c Qy)) +c Qyz) +c Pz.
  rewrite /b - !csumA; apply: f_equal.
  by rewrite csumC - !csumA (csumA Qyz Qy Pz) (csumC Qyz Qy) (csumA Qy Qyz Pz).
rewrite eq1 eq2 - !csumA; apply: f_equal; apply: f_equal.
by rewrite csumC (csumC _ Qxy) csumA.
Qed.

Lemma BZsum_AC x y z: intp x -> intp y -> intp z ->
  (x +z y) +z z = (x +z z) +z y.
Proof.
move => xz yz zz.
by rewrite - (BZsumA xz yz zz) - (BZsumA xz zz yz) (BZsumC y).
Qed.

Lemma BZsum_CA x y z: intp x -> intp y -> intp z ->
  x +z (y +z z) = y +z (x +z z).
Proof.
by move => xz yz zz;rewrite (BZsumA xz yz zz) (BZsumA yz xz zz) (BZsumC x y).
Qed.

Lemma BZsum_ACA a b c d: intp a -> intp b -> intp c -> intp d ->
    (a +z b) +z (c +z d) = (a +z c) +z (b +z d).
Proof.
move => az bz cz dz; move: (ZSs cz dz) (ZSs bz dz)=> cdz bdz.
by rewrite -!BZsumA // (BZsum_CA bz cz dz).
Qed.

(** ** difference *)

Definition BZdiff x y := x +z (BZopp y).

Notation "x -z y" := (BZdiff x y) (at level 50).

Definition BZsucc x  :=  x +z \1z.
Definition BZpred x  :=  x -z \1z.


Lemma ZS_diff x y: intp x -> intp y -> intp (x -z y).
Proof. by move => sa /ZSo sb;apply:ZSs. Qed.

Lemma ZS_succ x: intp x -> intp (BZsucc x).
Proof. move => xz; apply: (ZSs xz ZS1). Qed.

Lemma ZS_pred x: intp x -> intp (BZpred x).
Proof. move => xz; apply: (ZS_diff xz ZS1). Qed.

Lemma BZsucc_N x: natp x ->  BZsucc (BZ_of_nat x) = BZ_of_nat (csucc x).
Proof. 
move => xB; rewrite /BZsucc  (BZsum_pp (BZ_of_natp_i xB) (BZ_of_natp_i NS1)).
by rewrite ! BZ_of_nat_val (Nsucc_rw xB).
Qed.

Lemma BZprec_N x: inc x Nats ->  BZpred (BZ_of_nat x) = BZ_of_nat (cpred x).
Proof.
move /setC1_P => [pa pb]; move: (cpred_pr pa pb) => [qa qb].
move: (BZ_of_nat_i qa) => pc.
rewrite {1} qb - (BZsucc_N  qa) /BZsucc /BZpred /BZdiff.
by rewrite  - (BZsumA pc ZS1 (ZSo ZS1)) (BZsum_opp_r ZS1) BZsum_0r.
Qed.


Section BZdiffProps.
Variables (x y z: Set).
Hypotheses (xz: intp x)(yz: intp y)(zz: intp z).

Lemma BZsucc_sum : (BZsucc x +z y) = BZsucc (x +z y).
Proof. 
rewrite /BZsucc (BZsumC x)  (BZsumC _ \1z) BZsumA //; apply: ZS1.
Qed.

Lemma BZpred_sum: (BZpred x +z y) = BZpred (x +z y).
Proof. 
rewrite /BZpred/BZdiff (BZsumC x)  (BZsumC _ (BZopp \1z)).
rewrite BZsumA //; apply: (ZSo ZS1).
Qed.


Lemma BZsucc_pred : BZsucc (BZpred x) = x.
Proof. 
move: (ZSo ZS1) ZS1 => ha hb.
by rewrite /BZsucc /BZpred /BZdiff - BZsumA // BZsum_opp_l // BZsum_0r.
Qed.

Lemma BZpred_succ: BZpred (BZsucc x) = x.
Proof.  
move: (ZSo ZS1) ZS1 => ha hb.
by rewrite /BZsucc /BZpred /BZdiff - BZsumA // BZsum_opp_r // BZsum_0r.
Qed.

Lemma BZdiff_sum: (x +z y) -z x = y.
Proof. 
by rewrite /BZdiff BZsumC (BZsumA (ZSo xz) xz yz) BZsum_opp_l // BZsum_0l.
Qed.

Lemma BZsum_diff: x +z (y -z x) = y.
Proof. 
by rewrite /BZdiff (BZsumC y) (BZsumA xz (ZSo xz) yz) BZsum_opp_r // BZsum_0l. 
Qed.

Lemma BZdiff_sum1: (y +z x) -z x = y.
Proof. by rewrite (BZsumC y) BZdiff_sum. Qed.

Lemma BZsum_diff1: (y -z x) +z x = y.
Proof. by rewrite BZsumC BZsum_diff. Qed.

Lemma BZdiff_diag : x -z x = \0z.
Proof. by rewrite /BZdiff BZsum_opp_r. Qed.

Lemma BZdiff_0r: x -z \0z = x.
Proof. by rewrite /BZdiff BZopp_0 BZsum_0r. Qed.

Lemma BZdiff_0l: \0z -z x = BZopp x.
Proof. by rewrite /BZdiff  BZsum_0l //; apply:ZSo. Qed.

Lemma BZdiff_sum_simpl_l:  (x +z y) -z  (x +z z) = y -z z.
Proof.
rewrite /BZdiff (BZoppD xz zz) (BZsumC x y).
rewrite (BZsumA (ZSs yz xz) (ZSo xz) (ZSo zz)).
by rewrite  -(BZsumA yz xz (ZSo xz)) BZsum_opp_r // BZsum_0r.
Qed.

Lemma BZdiff_sum_comm: (x +z y) -z z = (x -z z) +z y.
Proof. 
by rewrite /BZdiff (BZsumC x y) (BZsumC _ y) - (BZsumA yz xz) //; apply: ZSo.
Qed.

Lemma BZoppB: BZopp (x -z y) = y -z x.
Proof.
rewrite /BZdiff (BZoppD xz (ZSo yz)). 
by rewrite (BZopp_K yz) BZsumC.
Qed.

End BZdiffProps.

Section BZdiffProps2.
Variables (x y z: Set).
Hypotheses (xz: intp x)(yz: intp y)(zz: intp z).

Lemma BZsucc_disc:  x <> BZsucc x.
Proof. 
move: ZS1 => pb pc.
move:(BZdiff_sum xz pb); rewrite - /(BZsucc x) - pc (BZdiff_diag xz) => h.
by case: BZ1_nz; rewrite h.
Qed.

Lemma BZsum_diff_ea: x = y +z z -> z = x -z y.
Proof.  by move => -> ; rewrite BZdiff_sum. Qed.

Lemma BZdiff_diag_rw:  x -z y = \0z -> x = y.
Proof. 
move => h; move:(f_equal (BZsum y) h).
by rewrite (BZsum_diff yz xz) BZsum_0r.
Qed.

Lemma BZdiff_sum_simpl_r:  (x +z z) -z (y +z z) = x -z y.
Proof. by rewrite (BZsumC x z) (BZsumC y z);  apply: BZdiff_sum_simpl_l. Qed.


Lemma BZdiff_succ_l: BZsucc (x -z y) =  (BZsucc x) -z y.
Proof. 
rewrite /BZsucc; symmetry; apply: BZdiff_sum_comm => //; apply: ZS1.
Qed.


Lemma BZsum_eq2r:  x +z z = y +z z -> x = y.
Proof.
move => h; rewrite - (BZdiff_sum zz xz) - (BZdiff_sum zz yz).
by rewrite BZsumC h BZsumC.
Qed.

Lemma BZsum_eq2l:  x +z y = x +z z -> y = z.
Proof.
by move => h; rewrite - (BZdiff_sum xz yz) - (BZdiff_sum xz zz) h.
Qed.

End  BZdiffProps2.


Lemma BZdiff_diff a b c: intp a -> intp b -> intp c ->
   a -z (b -z c)  = (a -z b) +z c.
Proof.
move => aq bq cq; rewrite /BZdiff.
rewrite (BZoppD bq (ZSo cq)) (BZopp_K cq) BZsumA //; exact: ZSo.
Qed.

Lemma BZdiff_diff2 a b c: intp a -> intp b -> intp c ->
   a -z (b +z c)  = (a -z b) -z c.
Proof.
move => aq bq cq.
by move:(BZdiff_diff aq bq (ZSo cq)); rewrite /BZdiff (BZopp_K cq).
Qed.



(** ** The sign function *)

Definition BZsign x:= Yo (BZ_val x = \0c) \0z (Yo (int_pp x) \1z \1mz).


Lemma BZsign_trichotomy a: BZsign a = \1z \/ BZsign a = \1mz \/ BZsign a = \0z.
Proof. rewrite /BZsign; Ytac pa; try Ytac pb; fprops. Qed.


Lemma ZS_sign x: inc (BZsign x) BZ.
Proof. 
move:ZS0 ZS1 ZSm1 => sa sb sc;rewrite /BZsign. 
by Ytac pa;[  | Ytac pb  ]. 
Qed.

Lemma BZsign_pos x: inc x BZps -> BZsign x = \1z.
Proof. 
by  rewrite /BZsign; move /indexed_P=> [_ ] /setC1_P [_ nz] q; Ytac0; Ytac0.
Qed.

Lemma BZsign_neg x: inc x BZms -> BZsign x = \1mz.
Proof. 
rewrite /BZsign /int_pp.
by  move /indexed_P=> [_] /setC1_P [_ nz] ->; Ytac0; Ytac0.
Qed.

Lemma BZsign_0: BZsign \0z = \0z.
Proof. by rewrite /BZsign BZ0_val; Ytac0. Qed.


Lemma BZopp_sign x: intp x -> BZsign (BZopp x) = BZopp (BZsign x).
Proof.
move => xz.
case/BZ_i1P:(xz) => xs.
+ by rewrite xs BZopp_0 BZsign_0 BZopp_0.
+ by rewrite (BZsign_pos xs) BZopp_1 BZsign_neg //; apply:BZopp_positive1.
+ by rewrite (BZsign_neg xs) BZopp_m1 BZsign_pos //;apply:BZopp_negative1.
Qed.

(** ** Multiplication *)

Definition BZprod_int x y :=
  let aux := BZ_of_nat ((BZ_val x) *c (BZ_val y)) in
     (Yo (BZ_sg x = BZ_sg y) aux (BZopp aux)).

Definition BZprod := locked BZprod_int.
Notation "x *z y" := (BZprod x y) (at level 40).

Lemma  BZprodE: BZprod  = BZprod_int.
Proof. by rewrite /BZprod - lock. Qed.
 

Definition BZprod_sign_aux x y:=  
  Yo (x = \0z) C1 (Yo (y= \0z) C1 (Yo (BZ_sg x = BZ_sg y) C1 C0)).

Lemma BZprodC x y: x *z y = y *z x.
Proof.
rewrite BZprodE /BZprod_int cprodC.
case: (equal_or_not (Q x) (Q y)); first by move => ->.
by move => h; move: (nesym h) => h1; Ytac0; Ytac0.
Qed.

Lemma BZprod_0r x: x *z \0z = \0z.
Proof. by rewrite BZprodE /BZprod_int BZ0_val cprod0r -/BZ_zero BZopp_0; Ytac xx. Qed.

Lemma BZprod_0l x: \0z *z x = \0z.
Proof. by rewrite BZprodC BZprod_0r. Qed.

Lemma BZprod_22: \2z *z \2z = \4z.
Proof.  
by rewrite BZprodE /BZprod_int/BZ_two/BZ_of_nat; aw; Ytac0; rewrite cprod_22.
Qed.

Lemma BZprod_val x y: BZ_val (x *z y) = (BZ_val x) *c (BZ_val y).
Proof. by rewrite BZprodE /BZprod_int;Ytac aux; rewrite ?BZopp_val BZ_of_nat_val. Qed.

Lemma BZprod_nz x y: intp x -> intp y ->
  x <> \0z -> y <> \0z -> x  *z y <> \0z.
Proof. 
move => xz yz xnz ynz zz.
move: (congr1 P zz); rewrite BZprod_val BZ0_val;  apply: cprod2_nz.
+ move => pz; case: xnz; apply: (BZ_0_if_val0 xz pz).
+ move => pz; case: ynz; apply: (BZ_0_if_val0 yz pz).
Qed.


Lemma BZprod_abs2 x y: intp x -> intp y ->  
  x *z y = J ((BZ_val x) *c (BZ_val y)) (BZprod_sign_aux x y).
Proof.
move => xz yz; rewrite /BZprod_sign_aux.
case: (equal_or_not x \0z).
  by move => ->;rewrite BZprod_0l BZ0_val cprod0l; Ytac0. 
move=> xnz;case: (equal_or_not y \0z).
  by move => ->;rewrite BZprod_0r BZ0_val cprod0r; Ytac0; Ytac0.
move => ynz; Ytac0; Ytac0.
move:(BZprod_nz xz yz xnz ynz).
rewrite BZprodE /BZprod_int ; Ytac qxy; Ytac0 => //. 
rewrite /BZopp /BZ_of_nat/ int_np; aw; Ytac0.
by rewrite /BZm_of_nat; Ytac ww.
Qed.


Lemma ZSp x y: intp x -> intp y ->  intp (x *z y).
Proof. 
move => pa pb.
move: (BZ_of_nat_i (NS_prod (BZ_valN pa)(BZ_valN pb))) => h.
rewrite BZprodE /BZprod_int;Ytac h1 => //; apply: ZSo => //.
Qed.

Lemma BZprod_pp x y: inc x BZp -> inc y BZp ->
    x *z y = BZ_of_nat ((BZ_val x) *c (BZ_val y)).
Proof.  by move => pa pb; rewrite BZprodE /BZprod_int (BZp_sg pa)(BZp_sg pb); Ytac0. Qed.

Lemma BZprod_cN x y: natp x ->  natp y -> 
  BZ_of_nat x *z BZ_of_nat y = BZ_of_nat (x *c y).
Proof.
move => pa pb.
rewrite (BZprod_pp (BZ_of_natp_i pa) (BZ_of_natp_i pb)).
by rewrite !BZ_of_nat_val.
Qed.


Lemma BZprod_mm x y: inc x BZms -> inc y BZms-> 
    x *z y = BZ_of_nat ((BZ_val x) *c (BZ_val y)).
Proof. by move => pa pb; rewrite BZprodE /BZprod_int (BZms_sg pa)(BZms_sg pb); Ytac0. Qed.


Lemma BZprod_pm x y: inc x BZp -> inc y BZms-> 
  x *z y = BZm_of_nat ((BZ_val x) *c (BZ_val y)).
Proof. 
move => pa pb; rewrite BZprodE /BZprod_int (BZp_sg pa)(BZms_sg pb).
by Ytac0;rewrite  /BZopp /BZ_of_nat /int_np pr2_pair; Ytac0; aw.
Qed.
 
Lemma BZprod_mp x y: inc x BZms -> inc y BZp -> 
  x *z y = BZm_of_nat ((BZ_val x) *c (BZ_val y)).
Proof. by move => pa pb; rewrite BZprodC;rewrite BZprod_pm // cprodC. Qed.


Lemma ZpS_prod a b: inc a BZp -> inc b BZp -> inc (a *z b) BZp.
Proof. 
move => az bz; rewrite (BZprod_pp az bz).
exact: (BZ_of_natp_i (NS_prod (BZ_valN (BZp_sBZ az))(BZ_valN (BZp_sBZ bz)))). 
Qed.


Lemma ZpsS_prod a b: inc a BZps -> inc b BZps -> inc (a *z b) BZps.
Proof. 
move => /BZps_iP [ap anz] /BZps_iP [bp bnz]; apply/BZps_iP ; split.
  by apply: ZpS_prod.  
by move:(BZp_sBZ ap) (BZp_sBZ bp) => az bz; apply:BZprod_nz.
Qed.

Lemma ZmsuS_prod a b: inc a BZms -> inc b BZms -> inc (a *z b) BZps.
Proof. 
move => az bz;apply/BZps_iP ; split.
  rewrite (BZprod_mm az bz); apply :BZ_of_natp_i. 
  by apply:NS_prod;apply:BZ_valN; apply: BZms_sBZ.
move/BZms_iP: az => [/BZm_sBZ az a0].
move/BZms_iP: bz => [/BZm_sBZ bz b0].
by apply:BZprod_nz. 
Qed.


Lemma ZmuS_prod a b: inc a BZm -> inc b BZm -> inc (a *z b) BZp.
Proof. 
case /setU1_P; last by move => -> _ ; rewrite BZprod_0l;  apply: ZpS0.
move => am;case /setU1_P; last by move -> ; rewrite BZprod_0r; apply: ZpS0.
move => bm; exact :( BZps_sBZp (ZmsuS_prod am bm)). 
Qed.

Lemma ZpmsS_prod a b: inc a BZps -> inc b BZms -> inc (a *z b) BZms.
Proof. 
move => az bz; move: (BZps_valnz az) (proj1 (BZms_hi_pr bz)) => anz bnz.
move: (BZ_valN (BZps_sBZ az)) (BZ_valN (BZms_sBZ bz)) => pa pb.
move /BZps_iP: az =>[ap _]; rewrite (BZprod_pm ap bz); apply: BZm_of_natms_i.
  by apply:NS_prod.
by apply cprod2_nz.
Qed.

Lemma ZpmS_prod a b: inc a BZp -> inc b BZm -> inc (a *z b) BZm.
Proof. 
move => az; case /setU1_P; last by move ->;  rewrite BZprod_0r;apply: ZmS0.
move => bz; case: (equal_or_not a \0z). 
  by move => ->; rewrite BZprod_0l;apply: ZmS0. 
move => anz; move /BZps_iP: (conj az anz) => sap.
by apply /setU1_P; left; apply: ZpmsS_prod.
Qed.

Lemma BZps_stable_prod1 a b: intp a -> intp b -> inc (a *z b) BZps ->
  ((inc a BZps <-> inc b BZps) /\ (inc a BZms <-> inc b BZms)).
Proof. 
move => az bz.
move:BZ_di_neg_spos => H.
case /BZ_i1P: az. 
+ by move => ->; rewrite BZprod_0l => /BZps_iP [_].
+ case /BZ_i1P: bz. 
- by move => -> _; rewrite BZprod_0r => /BZps_iP [_]  .
  - move => pa pb pc;split; split => // h; [case: (H _ h pb) | case:(H _ h pa)].
  - move => pa pb pc;case: (H _ _ pc); exact (ZpmsS_prod pb pa).
+ case /BZ_i1P: bz. 
  - by move => -> _; rewrite BZprod_0r => /BZps_iP [_].
  - move => pa pb /H []; rewrite BZprodC; exact (ZpmsS_prod pa pb).
  - move => pa pb pc.
    split; split => // h; [case: (H _ pb h) | case: (H _ pa h)].
Qed.


Lemma BZprod_1l x: intp x ->  \1z *z x = x.
Proof.
move => xz; move: (CS_nat (BZ_valN xz)) => cpx.
rewrite BZprodE /BZprod_int /BZ_one /BZ_of_nat /BZopp/int_np.
aw; rewrite cprod1l //;Ytac0.
case /BZ_i0P: xz => h. 
  by rewrite (BZms_sg h); Ytac0; apply:BZm_hi_pr; apply:BZms_sBZm.
by rewrite (BZp_sg h); Ytac0; apply:BZp_hi_pr.
Qed.

Lemma BZprod_1r x: intp x ->  x *z \1z  = x.
Proof. by move => pa; rewrite BZprodC; apply BZprod_1l. Qed.

Lemma BZprod_m1r x: intp x ->  x *z \1mz = BZopp x.
Proof. 
move => xz; move: (CS_nat (BZ_valN xz)) => h.
rewrite BZprodE /BZprod_int /BZ_mone /BZm_of_nat /BZ_of_nat /BZopp/int_np.
by rewrite (Y_false card1_nz); aw; rewrite cprod1r//; Ytac0; Ytac aux.
Qed.

Lemma BZprod_m1l x: intp x -> \1mz *z x  = BZopp x.
Proof. by  move => pa; rewrite  BZprodC; apply:  BZprod_m1r. Qed.

Lemma BZsign_abs x: intp x -> x *z (BZsign x) = BZabs x.
Proof. 
move => xz; move: (ZS_sign x) => xsp.
case /BZ_i1P: (xz) => xs; first by rewrite xs BZprod_0l BZabs_0.
  by rewrite (BZsign_pos xs) (BZabs_pos (BZps_sBZp xs)) BZprod_1r.
by rewrite (BZsign_neg xs) (BZabs_neg xs) (BZprod_m1r xz). 
Qed.


Lemma BZabs_sign x: intp x -> x =  (BZsign x) *z (BZabs x).
Proof.
move => xz; move: (ZSa xz) => az.
case /BZ_i1P: (xz) => xs; first by rewrite xs  BZabs_0 BZprod_0r. 
  by rewrite (BZsign_pos xs) (BZabs_pos (BZps_sBZp xs)) BZprod_1l.
by rewrite (BZsign_neg xs) (BZabs_neg xs) (BZprod_m1l (ZSo xz)) (BZopp_K xz).
Qed.

Lemma BZprod_abs x y: intp x -> intp y ->  
  BZabs (x *z y) = (BZabs x) *z (BZabs y).
Proof.
move => pa pb. 
rewrite (BZprod_pp (BZabs_iN pa)  (BZabs_iN pb)).
by rewrite (BZprod_abs2 pa pb) /BZabs /BZ_of_nat; aw.
Qed.

Lemma BZprod_sign x y: intp x -> intp y ->  
  BZsign (x *z y) = (BZsign x) *z (BZsign y).
Proof. 
move => xz yz.
case:(equal_or_not x \0z) => xnz. 
  by rewrite xnz BZprod_0l BZsign_0 BZprod_0l.
case:(equal_or_not y \0z) => ynz. 
  by rewrite ynz BZprod_0r BZsign_0 BZprod_0r.
rewrite (BZprod_abs2 xz yz) /BZprod_sign_aux /BZsign/int_pp  pr1_pair pr2_pair.
have pxnz: (P x) <> \0c by  move => h; case: xnz; exact (BZ_0_if_val0 xz h). 
have pynz: (P y) <> \0c by  move => h; case: ynz; exact (BZ_0_if_val0 yz h). 
move: (cprod2_nz pxnz pynz) => pxynz.
Ytac0; Ytac0; Ytac0; Ytac0; Ytac0.
move: ZS1 ZSm1 => ha hb.
case: (equal_or_not (Q x) (Q y)) => sq; Ytac0; Ytac0.
  by rewrite - sq; Ytac qa;rewrite ? BZprod_1r // (BZprod_m1r hb) BZopp_m1.
move: sq;case /BZ_sgv: xz => ->; Ytac0.
case /BZ_sgv: yz => ->; Ytac0 => //; rewrite ? (BZprod_1r ZSm1) //.
by case /BZ_sgv: yz => ->; Ytac0 => //; rewrite (BZprod_1l ZSm1).
Qed.

Lemma BZopp_prod_r x y: intp x -> intp y ->
  BZopp (x *z y) = x *z (BZopp y).
Proof. 
move => pa pb.
case /BZ_i1P: (pa). 
+ by move => ->; rewrite !BZprod_0l BZopp_0.
+ move => h1; case /BZ_i1P: pb => h2.
  - by rewrite h2  BZopp_0 !BZprod_0r BZopp_0.
  - move:(BZps_sBZp h1) => h3.
    rewrite (BZprod_pp h3 (BZps_sBZp h2)).
    by rewrite(BZprod_pm h3 (BZopp_positive1 h2)) BZopp_val BZopp_p.
  - rewrite (BZprod_pm (BZps_sBZp h1) h2).
    rewrite (BZprod_pp (BZps_sBZp h1) (BZps_sBZp  (BZopp_negative1 h2))).
    by rewrite BZopp_val BZopp_m.
+ move => h1; case /BZ_i1P: pb => h2.
  - by rewrite h2 BZopp_0 !BZprod_0r BZopp_0.
  - rewrite(BZprod_mp h1 (BZps_sBZp h2)). 
    by rewrite (BZprod_mm h1 (BZopp_positive1 h2))  BZopp_val BZopp_m.    
  - rewrite (BZprod_mm h1 h2) (BZprod_mp h1 (BZps_sBZp  (BZopp_negative1 h2))).
    by rewrite BZopp_val BZopp_p.
Qed.

Lemma BZopp_prod_l x y: intp x -> intp y ->
    BZopp (x *z y) = (BZopp x) *z y.
Proof. by move => pa pb; rewrite BZprodC (BZopp_prod_r pb pa)  BZprodC. Qed.

Lemma BZprod_opp_comm x y: intp x -> intp y ->
  x *z  (BZopp y) =  (BZopp x) *z y.
Proof.  move => pa pb; rewrite - BZopp_prod_l // BZopp_prod_r //. Qed.

Lemma BZprod_opp_opp x y: intp x -> intp y ->
  (BZopp x) *z (BZopp y) = x  *z y.
Proof. by move => pa pb; rewrite  (BZprod_opp_comm (ZSo pa) pb) BZopp_K. Qed.

Lemma BZprodA x y z: intp x -> intp y -> intp z ->
  x *z (y *z z) = (x *z y) *z z.
Proof.
move => pa pb pc;  move: (ZSp pa pb) (ZSp pb pc)  => pab pbc.
rewrite (BZprod_abs2 pa pbc) (BZprod_abs2 pab pc) BZprod_val BZprod_val cprodA.
congr (J _ _).
rewrite /BZprod_sign_aux.
Ytac xz; first by rewrite xz BZprod_0l; Ytac0.
case: (equal_or_not y \0z) => yz.
  by rewrite yz BZprod_0l BZprod_0r; Ytac0; Ytac0.
rewrite (Y_false (BZprod_nz pa pb xz yz)).
case: (equal_or_not z \0z) => zz; Ytac0; first by rewrite zz BZprod_0r; Ytac0. 
rewrite (Y_false (BZprod_nz pb pc yz zz)).
rewrite (BZprod_abs2 pa pb) (BZprod_abs2 pb pc) ! pr2_pair.
rewrite /BZprod_sign_aux; Ytac0; Ytac0; Ytac0; Ytac0.
have aux: forall t, inc t BZ -> Q t = C0 \/ Q t = C1.
   by move => t /candu2P [_]; case; move => [_]; [left | right].
by case /aux: pa => ->; case /aux: pb => ->;  case /aux: pc => ->;
    Ytac0; Ytac0; (try Ytac0) => //; Ytac0.
Qed.

Lemma BZprod_AC x y z: intp x -> intp y -> intp z ->
  (x *z y) *z z = (x *z z) *z y.
Proof.
move => xz yz zz.
by rewrite - (BZprodA xz yz zz) - (BZprodA xz zz yz) (BZprodC y).
Qed.

Lemma BZprod_CA x y z: intp x -> intp y -> intp z ->
  x *z (y *z z) = y *z (x *z z).
Proof.
by move => xz yz zz;rewrite (BZprodA xz yz zz) (BZprodA yz xz zz) (BZprodC x y).
Qed.

Lemma BZprod_ACA a b c d: intp a -> intp b -> intp c -> intp d ->
    (a *z b) *z (c *z d) = (a *z c) *z (b *z d).
Proof.
move => az bz cz dz; move: (ZSp cz dz) (ZSp bz dz)=>  cdz bdz.
by rewrite -!BZprodA // (BZprod_CA bz cz dz).
Qed.

Lemma BZprodDr n m p: intp n -> intp m -> intp p  ->
   n *z ( m +z p) = (n *z m) +z (n *z p).
Proof. 
move: n m p.
have Qa:forall n m p, inc n BZps -> inc m BZp -> inc p BZp
    -> n *z ( m +z p) = (n *z m) +z (n *z p).
  move => n m p pa pb pc.
  move: (BZps_sBZp pa) => pa'.
  move: (BZ_valN (BZp_sBZ pa'))(BZ_valN (BZp_sBZ pb))(BZ_valN (BZp_sBZ pc)).
  move => qa qb qc.
  move: (BZ_of_natp_i (NS_prod qa qb)) => qe.
  move: (BZ_of_natp_i (NS_prod qa qc)) => qf.
  rewrite (BZprod_pp pa' pb)(BZprod_pp pa' pc) (BZprod_pp pa' (ZpS_sum pb pc)).
  rewrite (BZsum_pp pb pc) (BZsum_pp qe qf)  !BZ_of_nat_val. 
  by rewrite cprodDr.
have Qb:forall n m p, inc n BZps -> inc m BZp -> inc p BZ
     -> n *z ( m +z p) = (n *z m) +z (n *z p).
  move => n m p pa pb; case /BZ_i0P; last by apply: Qa.
  move => pc; move: (BZps_sBZp pa) => pa'.
  move: (BZ_valN (BZp_sBZ pa'))(BZ_valN (BZp_sBZ pb))(BZ_valN (BZms_sBZ pc)).
  move => qa qb qc.
  move:  (BZps_valnz pa) => pa''.
  have nzp:P n *c P p <> \0c by move:(BZms_hi_pr pc) => [s1 _];apply: cprod2_nz.
  move: (BZ_of_natp_i (NS_prod qa qb)) => qe.
  move: (BZm_of_natms_i (NS_prod qa qc) nzp) => qf.
  rewrite(BZsum_pm pb pc)(BZprod_pp pa' pb)(BZprod_pm pa' pc) (BZsum_pm qe qf).
  rewrite BZm_of_nat_val BZ_of_nat_val.
  case: (cleT_el (CS_nat qc) (CS_nat qb)) => le1.
     have le2: (P n *c P p <=c P n *c P m) by apply: cprod_Mlele; fprops.
     Ytac0; Ytac0; rewrite (BZprod_pp pa' (BZ_of_natp_i (NS_diff _ qb))).
     by rewrite BZ_of_nat_val (cprodBl qa qb qc).
  have le1':= cltNge le1.
  have le2': ~(P n *c P p <=c P n *c P m).
    by move => bad; move: (cprod_le2l qa qc qb pa'' bad).
  move: (NS_diff (P m) qc) => dB.
  Ytac0; Ytac0;rewrite (BZprod_pm pa' (BZm_of_natms_i dB (cdiff_nz le1))).
  by rewrite BZm_of_nat_val (cprodBl qa qc qb).
have Qc:forall n m p, inc n BZps -> inc m BZ -> inc p BZ
     -> n *z ( m +z p) = (n *z m) +z (n *z p).
  move => n m p pa pb pc.
  case /BZ_i0P: pb => mn; last by apply: Qb.
  move: (BZms_sBZ mn) (BZps_sBZ pa) => mz nz.
  move: (Qb _ _ _ pa (BZps_sBZp(BZopp_negative1 mn))  (ZSo pc)).
  move: (ZSs mz pc) (ZSp nz mz) (ZSp nz pc) => sz sa sb.
  rewrite - (BZoppD mz pc).
  rewrite - (BZopp_prod_r nz sz) - (BZopp_prod_r nz mz) - (BZopp_prod_r nz pc).
  by rewrite - (BZoppD sa sb);apply:BZopp_inj; [ apply: ZSp | apply: ZSs].
have Qd: (forall x y, intp x -> intp y ->  (BZopp y) *z x = BZopp (y *z x)).
  by move => x y xz yz; rewrite (BZopp_prod_r yz xz) (BZprod_opp_comm yz xz).
move => n m p.
case /BZ_i1P ; first by move => -> _ _; rewrite !BZprod_0l (BZsum_0r ZS0).
  by apply: Qc.
move => nz' mz pz; move: (BZopp_negative1 nz') (BZms_sBZ nz') => nz'' nz.
move: (BZps_sBZ nz'') => oz.
rewrite - (BZopp_K nz).
rewrite (Qd _ _   (ZSs mz pz) oz)  (Qd _ _ mz oz)  (Qd _ _ pz oz).
by rewrite (Qc _ _ _ nz'' mz pz) BZoppD //; apply:ZSp.
Qed.

Lemma BZprodDl n m p: intp n -> intp m -> intp p ->
   ( m +z p) *z n = (m *z n) +z (p *z n).
Proof.
by move => pa pb pc; rewrite (BZprodC)  (BZprodC m) (BZprodC p);apply:BZprodDr.
Qed.


Lemma BZprodBr x y z: intp x -> intp y -> intp z  ->
   x *z (y -z z) = (x *z y) -z (x *z z).
Proof. 
move => xz yz zz; rewrite /BZdiff (BZprodDr xz yz (ZSo zz)). 
by rewrite BZopp_prod_r. 
Qed.

Lemma BZprodBl x y z: intp x -> intp y -> intp z  ->
  (y -z z) *z x =  (y *z x) -z  (z *z x).
Proof. 
by move => xz yz zz; rewrite BZprodC (BZprodC y)  (BZprodC z) BZprodBr.
Qed.

Lemma BZdoublep x: intp x -> \2z *z x = x +z x.
Proof.
by move => xz; rewrite -BZsum_11 (BZprodDl xz ZS1 ZS1) (BZprod_1l xz). 
Qed.

Lemma BZprod_eq2r x y z: intp x -> intp y -> intp z  -> z <> \0z ->
   x *z  z =  y *z z ->  x = y.
Proof. 
move => xz yz zz znz eq; apply: (BZdiff_diag_rw xz yz); ex_middle bad.
case: (BZprod_nz (ZS_diff xz yz) zz bad znz).
by move:(BZprodBl zz xz yz); rewrite eq (BZdiff_diag (ZSp yz zz)).
Qed.

Lemma BZprod_eq2l x y z: intp x -> intp y -> intp z  -> z <> \0z ->
   z *z x =  z *z y ->  x = y.
Proof. 
by move => xz yz zz znz; rewrite BZprodC (BZprodC z); apply: BZprod_eq2r.
Qed.


Lemma BZprod_1_inversion_l x y : intp x -> intp y -> x *z y = \1z ->
   (x = y /\ (x = \1z \/ x = \1mz)).
Proof. 
move => xz yz eq1.
move: (sym_eq (BZprod_val x y)); rewrite eq1 BZ_of_nat_val => eq2.
move :(BZ_valN xz) (BZ_valN yz) => pa pb.
move:(cprod_eq1 (CS_nat pa) (CS_nat pb) eq2) => [ea eb].
move /candu2P: xz => [prx]; case; move => [_ h].
  have x1: x = \1mz by rewrite /BZ_mone/BZm_of_nat(Y_false card1_nz) -prx ea h.
  move: (BZprod_m1l yz); rewrite - x1 eq1 {1} x1 - BZopp_1 => ->.
  by rewrite (BZopp_K yz); split => //; right.
have x1: x = \1z by rewrite /BZ_one/BZ_of_nat;apply:pair_exten; fprops; aw.
by move: eq1; rewrite x1 (BZprod_1l yz) => ->; split => //; left.
Qed.

Lemma BZprod_1_inversion_s x y : intp x -> intp y -> x *z y = \1z ->
   (BZabs y = \1z).
Proof. 
move => pa pb pc; move:(BZprod_1_inversion_l pa pb pc) => [->].
by case => ->; rewrite ? BZabs_1 ? BZabs_m1.
Qed.

Lemma BZprod_1_inversion_more a b c:
  intp a -> intp b -> intp c -> a = a *z (b *z c) ->
  [\/ a = \0z, b = \1z | b = \1mz].
Proof. 
move => az bz cz.
rewrite - {1} (BZprod_1r az) => h.
case: (equal_or_not a \0z) => anz;first by constructor 1.
move: (BZprod_eq2l ZS1 (ZSp bz cz) az anz h) => h1; symmetry in h1.
move: (BZprod_1_inversion_l bz cz h1) => [_]; case =>H; in_TP4.
Qed.

Lemma BZprod_succ_r  n m: intp n -> intp m ->
   n *z (BZsucc m) = (n *z m)  +z n.
Proof.
by move => pa pb; rewrite /BZsucc (BZprodDr pa pb ZS1) BZprod_1r. 
Qed.

Lemma BZprod_succ_l n m: intp n -> intp m ->
  (BZsucc n) *z m = (n *z m) +z m.
Proof. by  move => pa pb; rewrite BZprodC (BZprod_succ_r pb pa) BZprodC. Qed.

Lemma zle_diffP a b: intp a -> intp b ->  (a <=z b <-> inc (b -z a) BZp).
Proof. 
pose aux a b := (a <=z b <-> inc (b -z a) BZp).
move: a b.
have Ha: (forall a b, inc a BZp -> inc b BZp -> aux a b).
  move => a b az bz.
  move: (BZp_sBZ bz) => bz1.
  move: (BZ_valN (BZp_sBZ az))  (BZ_valN bz1) => pa pb.
  rewrite /aux; apply: (iff_trans (zle_P1 az bz)).
  case: (equal_or_not a \0z) => anz.
    rewrite anz /BZdiff BZopp_0 BZsum_0r // BZ0_val;split => h //.
    apply:(cle0n pb).
  have az1: inc a BZps by apply /BZps_iP.
  move:(BZopp_positive1 az1) => az2;rewrite /BZdiff.
  move: (BZopp_val a)=> eq0.
  case: (cleT_el (CS_nat pa) (CS_nat pb)) => ce1.
     split; [move => _ |  by done].
     move: (BZsum_pm1 bz az2); rewrite eq0 => h; rewrite (h  ce1).
     by apply: BZ_of_natp_i; apply: NS_diff.
  split; first by move/(cltNge ce1).
  move: (cdiff_nz ce1) => ne1.
  rewrite -eq0 in ce1; rewrite  (BZsum_pm2 bz az2 ce1); rewrite eq0.
  rewrite /BZm_of_nat;Ytac0 => bad.
  by move:(BZp_sg bad);rewrite/int_pp;aw => ba;case:C0_ne_C1.
have Hb: (forall a b, inc a BZ -> inc b BZp -> aux a b).
  move => a b pa pb;case /BZ_i0P: pa => ap; last by apply: Ha.
  split => _; first by apply: (ZpS_sum pb (BZps_sBZp (BZopp_negative1 ap))).
  exact (proj1 (zle_pr2 pb ap)).
move => a b az bz.
case /BZ_i0P: (bz) => bz1; last by apply: Hb.
case /BZ_i0P: (az) => az1; last first.
  split; move => ha; first by case: (zle_pr4 az1 bz1).
  by move:(BZ_di_neg_pos (ZmsS_sum_l bz1 (BZopp_positive2 az1)) ha).
move: (BZps_sBZp (BZopp_negative1 az1)) => tt.
move: (Hb _ _ (ZSo bz) tt) => aux1.
have ->: b -z a = (BZopp a -z BZopp b) by rewrite /BZdiff BZsumC (BZopp_K bz).
split => ha.
  by move: (zle_opp ha); move /aux1. 
by move/aux1: ha => hb; move: (zle_opp hb); rewrite (BZopp_K az)(BZopp_K bz).
Qed.

Lemma zle_diffP1 a b: intp a -> intp b -> 
  (\0z <=z (b -z a) <-> a <=z b).
Proof. 
move => pa pb; move:(zle_diffP pa pb)(@zle0xP (b -z a)) => sa sb.
by split; [ move /sb/sa | move /sa/sb ].
Qed.

Lemma zlt_diffP a b: intp a -> intp b -> 
  (a <z b <-> inc (b -z a) BZps).
Proof.
move => pa pb; split.
  move => [/(zle_diffP pa pb)] pc pd; apply /BZps_iP;split => //.
  dneg aux; symmetry; exact (BZdiff_diag_rw pb pa aux).
move /BZps_iP => []  /(zle_diffP pa pb) pc pd; split => //.
by dneg aux; rewrite aux (BZdiff_diag pb).
Qed.

Lemma zlt_diffP1 a b: intp a -> intp b -> 
  (\0z  <z (b -z a) <-> a <z b).
Proof. 
move => pa pb; move:(zlt_diffP pa pb)(@zlt0xP (b -z a)) => sa sb.
by split; [ move /sb/sa | move /sa/sb ].
Qed.

Lemma zlt_diffP2 a b: intp a -> intp b -> 
  (a <z b <-> inc (a -z b) BZms).
Proof. 
move => pa pb; apply: (iff_trans (zlt_diffP pa pb)).
rewrite - (BZoppB pb pa); split => h.
  by apply: BZopp_positive1. 
rewrite - (BZopp_K (ZS_diff pb pa)); apply: (BZopp_negative1 h).
Qed.

Lemma BZsum_le2l a b c: intp a -> intp b -> intp c -> 
  ((c +z a) <=z (c +z b) <-> a <=z b).
Proof. 
move => pa pb pc.
apply: (iff_trans (zle_diffP (ZSs pc pa) (ZSs pc pb))).
apply: iff_sym; apply: (iff_trans (zle_diffP pa pb)); 
by rewrite BZdiff_sum_simpl_l.
Qed.

Lemma BZsum_le2r a b c: intp a -> intp b -> intp c ->
  ((a +z c) <=z (b +z c)  <-> a <=z b).
Proof. 
by move => pa pb pc; rewrite (BZsumC a c) (BZsumC b c); apply: BZsum_le2l. 
Qed.

Lemma BZsum_lt2l a b c: intp a -> intp b -> intp c -> 
  ((c +z a) <z (c +z b) <-> a <z b ).
move => pa pb pc.
apply: (iff_trans (zlt_diffP (ZSs pc pa) (ZSs pc pb))).
 apply: iff_sym;apply: (iff_trans (zlt_diffP pa pb)).
by rewrite BZdiff_sum_simpl_l.
Qed.

Lemma BZsum_lt2r a b c: intp a -> intp b -> intp c ->
   ( a +z c <z b +z c <-> a <z b).
Proof. 
by move => pa pb pc; rewrite (BZsumC a c) (BZsumC b c); apply: BZsum_lt2l. 
Qed.

Lemma BZ_induction_pos a (r:property): 
  (r a) -> (forall n,  a <=z n -> r n -> r (BZsucc n)) ->
  (forall n, a <=z n -> r n).
Proof. 
move => pb pc n h; move: (h) => [pa pd _].
move /(zle_diffP pa pd):h => dp.
rewrite - (BZsum_diff pa pd) BZsumC - (BZp_hi_pr dp).
move : (BZ_valN (BZp_sBZ dp)) => xn.
pose s n  := r ((BZ_of_nat n) +z a); rewrite -/(s _).
apply: (Nat_induction _ _ xn); first by rewrite /s -/BZ_zero BZsum_0l.
move => m mb; move:(BZ_of_natp_i mb) => aux1; move: (BZp_sBZ aux1) => aux.
have : a <=z (BZ_of_nat m +z a).  
  by apply/(zle_diffP pa (ZSs aux pa)); rewrite BZsumC (BZdiff_sum pa aux).
rewrite /s - (BZsucc_N mb) (BZsucc_sum (BZ_of_nat_i mb) pa);apply:pc. 
Qed.

Lemma BZ_induction_neg a (r:property): 
  (r a) -> (forall n,  n <=z a -> r n -> r (BZpred n)) ->
  (forall n, n <=z a -> r n).
Proof.
move => pb pc n h; move: (h) => [pa pd _].
move: (zle_opp h) => pe.
rewrite - (BZopp_K pa); pose s n:= r (BZopp n); rewrite -/(s _).
move: pb ; rewrite - (BZopp_K pd); rewrite -/(s _) => sa.
apply:  (BZ_induction_pos sa _ pe).
move => m le1; move: (zle_opp le1); rewrite (BZopp_K pd) /s /BZsucc. 
rewrite (BZoppD (proj32 le1) ZS1); apply: pc. 
Qed.

Lemma BZ_ind1 a (p:property): 
  intp a -> p a ->
  (forall x, BZ_le a x -> p x -> p (BZsucc x)) ->
  (forall x, BZ_le x a -> p x -> p (BZpred x)) -> 
  forall n, inc n BZ -> p n.
Proof. 
move => az pa pb pc n nz; case: (zleT_ee az nz). 
  by apply:BZ_induction_pos.
by apply:BZ_induction_neg.
Qed.

Lemma BZ_ind (p:property): 
  p \0z ->
  (forall x, intp x -> p x -> p (BZsucc x)) ->
  (forall x, intp x -> p x -> p (BZpred x)) -> 
  forall n, inc n BZ -> p n.
Proof. 
move: ZS0 => pa pb pc pd n nz; apply: (BZ_ind1 pa pb _ _ nz).
  by move=> x [_ xb _]; apply: pc.
by move=> x [xb _ _]; apply: pd.
Qed.


(** More comparison *)

Lemma BZsum_Mlele a b c d: a <=z c ->  b <=z d -> (a +z b) <=z (c +z d).
Proof.
move => eq1 eq2; move: (proj32 eq1)  (proj31 eq2)=> cz bz.
move /(BZsum_le2r (proj31 eq1) cz bz): eq1 => eq3.
move/(BZsum_le2l bz (proj32 eq2) cz): eq2 => eq4.
BZo_tac.
Qed.

Lemma BZsum_Mlelt a b c d: a <=z c -> b <z d -> (a +z b) <z (c +z d).
Proof.
move => eq1 eq2; move: (proj32 eq1)  (proj31_1 eq2)=> cz bz.
move /(BZsum_le2r (proj31 eq1) cz bz): eq1 => eq3.
move/(BZsum_lt2l bz (proj32_1 eq2) cz): eq2 => eq4.
BZo_tac.
Qed.

Lemma BZsum_Mltle a b c d: a <z c -> b <=z d -> (a +z b) <z (c +z d).
Proof.
by move => eq1 eq2; rewrite (BZsumC a)(BZsumC c); apply:BZsum_Mlelt.
Qed.

Lemma BZsum_Mltlt a b c d: a <z c -> b <z d -> (a +z b) <z (c +z d).
Proof. by move => eq1 [eq2 _]; apply: BZsum_Mltle. Qed.


Lemma BZsum_Mlege0 a c d: a <=z c ->  \0z <=z d -> a <=z (c +z d).
Proof.
move => pa pb; move: (BZsum_Mlele pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mlegt0 a c d: a <=z c ->  \0z <z d -> a <z (c +z d).
Proof.
move => pa pb; move: (BZsum_Mlelt pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mltge0 a c d: a <z c ->  \0z <=z d -> a <z (c +z d).
Proof.
move => pa pb; move: (BZsum_Mltle pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mltgt0 a c d: a <z c ->  \0z <z d -> a <z (c +z d).
Proof.
move => pa pb; move: (BZsum_Mltlt pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mlele0 a b c : a <=z c ->  b <=z \0z -> (a +z b) <=z c.
Proof. 
move => pa pb; move: (BZsum_Mlele pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mlelt0 a b c : a <=z c ->  b <z \0z -> (a +z b) <z c.
Proof. 
move => pa pb; move: (BZsum_Mlelt pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mltle0 a b c : a <z c ->  b <=z \0z -> (a +z b) <z c.
Proof. 
move => pa pb; move: (BZsum_Mltle pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mltlt0 a b c : a <z c ->  b <z \0z -> (a +z b) <z c.
Proof. 
move => pa pb; move: (BZsum_Mltlt pa pb); rewrite BZsum_0r //; BZo_tac.
Qed.

Lemma BZsum_Mp a b: intp a -> inc b BZp ->  a <=z (a +z b).
Proof. 
move => pa pb.
move /zle0xP: pb => eq1; exact:(BZsum_Mlege0 (zleR pa) eq1).
Qed.

Lemma BZsum_Mps a b: intp a -> inc b BZps ->  a <z (a +z b).
Proof. 
move => pa pb.
move /zlt0xP: pb => eq1; exact:(BZsum_Mlegt0 (zleR pa) eq1).
Qed.

Lemma BZsum_Mm a b: intp a -> inc b BZm ->  (a +z b) <=z a.
Proof. 
move => pa pb.
by move /zge0xP: pb => eq1; move:(BZsum_Mlele0 (zleR pa) eq1).
Qed.

Lemma BZsum_Mms a b: intp a -> inc b BZms ->  (a +z b) <z a.
Proof. 
move => pa pb.
by move /zgt0xP: pb => eq1; move:(BZsum_Mlelt0 (zleR pa) eq1).
Qed.

Lemma zlt_succ n: intp n -> n <z (BZsucc n).
Proof. 
move => nz; rewrite /BZsucc; apply: BZsum_Mps => //; apply: ZpsS1.
Qed.

Lemma zlt_pred n: intp n -> (BZpred n) <z n.
Proof. 
by move => nz; rewrite -{2} (BZsucc_pred nz);apply: zlt_succ;apply: ZS_pred.
Qed.

Lemma zlt_succ1P a b: intp a -> intp b ->
  (a <z (BZsucc b) <-> a <=z b).
Proof.
move => az bz.
apply:(iff_trans (zlt_diffP az (ZS_succ bz))).
apply: iff_sym; apply: (iff_trans (zle_diffP az bz)).
rewrite - (BZdiff_succ_l bz az); split => h.
  apply:(ZpsS_sum_r h ZpsS1).
have ha:= (BZp_hi_pr (BZps_sBZp h)).
move: (ZS_diff bz az) => cz; move:(BZpred_succ cz) =>  pc1.
move: h => /indexed_P [_ pc _].
move: (BZprec_N pc); rewrite ha pc1 => ->; apply: BZ_of_natp_i.
by move /setC1_P:pc => [pd pe]; move: (cpred_pr pd pe) => [].
Qed.

Lemma zlt_succ2P a b:  intp a -> intp b -> 
    (BZsucc a <=z b <-> a <z b).
Proof.
move => az bz.
have H := (zlt_succ1P (ZS_succ az) bz).
have Ha := zlt_diffP az bz.
have Hb := (zlt_diffP (ZS_succ az) (ZS_succ bz)).
have eq:= (BZdiff_sum_simpl_r bz az ZS1).  
split.
   by move/H /Hb; rewrite eq => /Ha.
by move /Ha; rewrite - eq => /Hb /H.
Qed.


Lemma zlt_pred1P a b: intp a -> intp b ->
    (a <z b) <-> a <=z (BZpred b).
Proof. 
by move => az bz; move: (zlt_succ1P az (ZS_pred bz)); rewrite BZsucc_pred.
Qed.
  
Lemma zlt_pred2P a b:  intp a -> intp b -> 
    (a <=z b <-> (BZpred a) <z b).
Proof.
by move => az bz; move: (zlt_succ2P (ZS_pred az) bz); rewrite BZsucc_pred.
Qed.


Lemma zleSSP a b: intp a -> intp b ->
    (a <=z b <-> BZsucc a <=z BZsucc b).
Proof.
move => ha hb; exact:(iff_sym (BZsum_le2r ha hb ZS1)).
Qed.

Lemma zleSSmP a b: intp a -> intp b ->
    (a <=z b <-> BZpred a <=z BZpred b).
Proof.
move => ha hb; exact:(iff_sym (BZsum_le2r ha hb (ZSo ZS1))).
Qed.


Lemma zle_abs n: intp n -> n <=z (BZabs n).
Proof. 
move => nz;case /BZ_i0P: (nz).
  move => nn; exact (proj1 (zle_pr2 (BZabs_iN nz) nn)).
by move => np; rewrite (BZabs_pos np); apply:zleR.
Qed.

Lemma zle_triangular n m: intp n -> intp m -> 
  (BZabs (n +z m)) <=z (BZabs n) +z (BZabs m).
Proof.
move: n m.
pose aux n m := BZabs (n +z m) <=z BZabs n +z BZabs m.
suff: forall n m, inc n BZp -> intp m -> aux  n m.
  move => h n m; case /BZ_i0P; last by apply: h.
  move => pa pb; rewrite - (BZabs_opp) - (BZabs_opp n)- (BZabs_opp m).
  rewrite (BZoppD (BZms_sBZ pa) pb); apply: h; last by apply: (ZSo pb).
  apply:(BZopp_negative2 (BZms_sBZm pa)).
move => n m np; case  /BZ_i0P; last first.
  move => mp; rewrite /aux (BZabs_pos np) (BZabs_pos mp).
  move:(ZpS_sum np mp) => pa; move: (BZp_sBZ pa) => pb.
  rewrite (BZabs_pos pa); apply: (zleR pb).
move => mn.
move: (BZp_sBZ np) (BZms_sBZ mn) => nz mz.
move: (BZ_valN nz) (BZ_valN mz) => pn pm.
rewrite /aux  (BZabs_pos np)  (BZabs_neg mn).
have [re1 _]: n<z n +z BZopp m. 
  by move: (BZsum_Mps nz (BZopp_negative1 mn)).
have re2: BZopp m  <=z n +z BZopp m. 
  rewrite BZsumC; exact(BZsum_Mp (ZSo mz) np).
case: (cleT_el (CS_nat pm) (CS_nat pn)) => ce1.
   rewrite (BZsum_pm1 np mn ce1);  move: (cdiff_ab_le_a (P m) (CS_nat pn)).
   set k := P n -c P m => ce2; rewrite /BZabs /BZ_of_nat; aw.
   have kz: inc (J k C1) BZp by apply: indexed_pi => //;apply: NS_diff.
   have le2:  P (J k C1) <=c P n by aw.
   move/ (zle_P1 kz np): le2 => le3; BZo_tac.
rewrite (BZsum_pm2 np mn ce1);  move: (cdiff_ab_le_a (P n) (CS_nat pm)).
move: (cdiff_nz ce1); set k := P m -c P n => knz ce2. 
rewrite /BZabs /BZm_of_nat; Ytac0; aw.
have kz: inc (J k C1) BZp by apply: indexed_pi => //;apply:NS_diff.
have le2:  P (J k C1) <=c P (BZopp m) by rewrite BZopp_val; aw.
move: (BZps_sBZp (BZopp_negative1 mn)) => omp.
move / (zle_P1 kz omp): le2 => le3; BZo_tac.
Qed.


Lemma BZ_order_isomorphism_P f:
 (order_isomorphism f BZ_order BZ_order) <->
 (exists2 u, intp u & f = Lf (fun z => z +z u) BZ BZ).
Proof. 
pose p a :=  Lf (fun z => z +z a) BZ BZ.
have Ha: forall a, intp a -> lf_axiom (fun z => z +z a) BZ BZ.
  by move => a az t tz; apply:ZSs.
have Hb: forall a, intp a -> bijection (p a).
  move => a az; apply: lf_bijective; first by apply: Ha.
    by move => u v uz vz; apply:(BZsum_eq2r uz vz az).
  move => y ye; exists (y -z a); first by apply:ZS_diff.
  by rewrite BZsumC BZsum_diff.
have Hc: forall a b c, intp a -> b <=z c -> (Vf (p a) b) <=z (Vf (p a) c).
  move => a b c az le1;move: (Ha _ az) => h; move: (le1) => [pa pb _].
  by rewrite /p !LfV//; apply /(BZsum_le2r pa pb az).
have Hd: (forall a, intp a -> order_isomorphism (p a)BZ_order BZ_order).
  move => a az.
  move: BZor_tor BZor_sr => to1 sor; move: (to1) => [or1 _].
  have hh:{inc BZ &, fincr_prop (Lf (BZsum^~ a) BZ BZ) BZ_order BZ_order}.
    move => u v uz vz /= /zle_P cuv; apply /zle_P; apply: Hc az cuv.
  by apply:(total_order_isomorphism to1 or1 (Hb _ az)); rewrite /p; aw.
split; last by move => [u uz ->]; apply: Hd.
move => [_ _ [bf sf tf] incf].
move: sf tf; rewrite BZor_sr => sf tf.
have He: (forall a b,  a <=z  b -> (Vf f a)  <=z (Vf f b)).
  move => a b ab;move: (ab) => [pa pb _]; move:ab; move/zle_P.
  by rewrite /intp - sf in pa pb;  move /(incf _ _ pa pb) /zle_P.
have Hf: (forall a b,  a <z  b -> (Vf f a) <z (Vf f b)).
  move => a b [pa pb]; split; first by apply: He.
  dneg pc; move: (pa) => [xa xb _]; rewrite /intp - sf in xa xb.
  exact: (bij_inj bf xa xb pc).
have Sa: forall x, intp x -> Vf f (BZsucc x) = (BZsucc (Vf f x)).
  rewrite /intp;move => x xz.
  have pa: inc  (Vf f x) BZ by Wtac; fct_tac.
  move: (ZS_succ pa); rewrite /intp - tf => pb; move: (bij_surj bf pb) => [m].
  rewrite sf;move => mf mv; suff: m = BZsucc x by move => <-.
  move: (Hf _ _ (zlt_succ xz)) => le1.
  case: (zleT_el mf (ZS_succ xz))=> le2; last first.
     move:(Hf _ _ le2); rewrite - mv; move /(zlt_succ1P (proj32_1 le1) pa).
     move => le3; BZo_tac.
  ex_middle ok; move /(zlt_succ1P mf xz): (conj le2 ok) => le3. 
  move: (He _ _ le3); rewrite - mv => l1; move: (zlt_succ pa) => l2; BZo_tac.
have Sb: forall x, intp x -> Vf f (BZpred x) = (BZpred (Vf f x)).
  move => x xz; move: (ZS_pred xz); rewrite /intp => pxz.
  rewrite -{2}(BZsucc_pred xz)(Sa _ pxz) BZpred_succ /intp // -tf;Wtac; fct_tac.
have fz: inc (Vf f \0z) BZ by rewrite -tf;Wtac;[fct_tac |rewrite sf; apply:ZS0].
exists  (Vf f \0z)  => //.
rewrite -/(p _); move: (Ha _ fz)(Hb _ fz);  set g := p (Vf f \0z).
move => Sc Sd.
apply: function_exten; try fct_tac. 
    by rewrite /g /p;aw.
  by rewrite /g /p;aw.
rewrite sf;move => u usf /=.
apply:(BZ_ind (p:= fun z => Vf f z = Vf g z)) => //.
    rewrite /g /p LfV//; [rewrite BZsum_0l // |  apply: ZS0].
  move => x xb; move: (ZS_succ xb) => sxb. 
  by rewrite (Sa _ xb); move => ->;rewrite /g /p !LfV// (BZsucc_sum xb fz).
move => x xb; move: (ZS_pred xb) => sxb. 
by rewrite (Sb _ xb); move => ->; rewrite /g /p ! LfV// (BZpred_sum xb fz).
Qed.

Definition consecutive r x y := 
   glt r x y /\ forall z, inc z (substrate r) -> ~( glt r x z /\ glt r z y).

Definition or_succ r x := select (fun z => consecutive r x z) (substrate r).
Definition or_pred r x := select (fun z => consecutive r z x) (substrate r).

Lemma conseq_unique_right r x y y': total_order r -> 
  consecutive r x y -> consecutive r x y' -> y = y'.
Proof.
move => [or tor] [ha hb] [hc hd].
ex_middle neq.
have ysr: inc y (substrate r) by order_tac.
have ysr': inc y' (substrate r) by order_tac.
case: (tor _ _ ysr ysr') => le1; first by case (hd _ ysr). 
case: (hb _ ysr'); split => //; split; fprops.
Qed.


Lemma conseq_unique_left r x x' y: total_order r -> 
  consecutive r x y -> consecutive r x' y -> x = x'.
Proof.
move => [or tor] [ha hb] [hc hd].
ex_middle neq.
have xsr: inc x (substrate r) by order_tac.
have xsr': inc x' (substrate r) by order_tac.
case: (tor _ _ xsr xsr') => le1; first by case: (hb _ xsr'). 
case: (hd _ xsr); split => //; split; fprops.
Qed.

Lemma or_succ_prop r x: total_order r -> 
   (exists y, consecutive r x y) -> consecutive r x (or_succ r x).
Proof.
move => sa sb. 
have pa: (exists2 y, inc y (substrate r) & consecutive r x y).
  move: sb => [y ya]; move: (ya) => [la _]; exists y => //; order_tac.
have pb:singl_val2 (inc^~ (substrate r)) (consecutive r x).
  move => u v _ up _ vp; apply: (conseq_unique_right sa up vp).
exact: (proj1 (select_pr  pa pb)).
Qed.

Lemma or_pred_prop r x: total_order r -> 
   (exists y, consecutive r y x) -> consecutive r (or_pred r x) x.
Proof.
move => sa sb. 
have pa: (exists2 y, inc y (substrate r) & consecutive r y x).
  move: sb => [y ya]; move: (ya) => [la _]; exists y => //; order_tac.
have pb:singl_val2 (inc^~ (substrate r)) (fun z =>  consecutive r z x).
  move => u v _ up _ vp; apply: (conseq_unique_left sa up vp).
exact: (proj1 (select_pr  pa pb)).
Qed.

Lemma or_succ_prop' r x y: total_order r -> 
  consecutive r x y ->  y = or_succ r x.
Proof.
move => pa pb; apply:(conseq_unique_right pa pb); apply: (or_succ_prop pa).
by exists y.
Qed.

Lemma or_pred_prop' r x y: total_order r -> 
  consecutive r x y ->  x = or_pred r y.
Proof.
move => pa pb; apply:(conseq_unique_left pa pb); apply: (or_pred_prop pa).
by exists x.
Qed.

Lemma BZ_succ_pred (r := BZ_order) x: intp x ->
  [/\ consecutive r x (BZsucc x), consecutive r (BZpred x) x,
      or_succ r x = BZsucc x & or_pred r x = BZpred x].
Proof.
move => xz.
have pa: consecutive r x (BZsucc x).
  split; first by apply /zlt_P; apply: zlt_succ.
  rewrite BZor_sr => z zz [/zlt_P ha /zlt_P /(zlt_succ1P zz xz) hb]; BZo_tac.
have pb: consecutive r (BZpred x) x.
  split; first by apply/zlt_P; apply /zlt_pred.
  rewrite BZor_sr => z zz [/zlt_P ha /zlt_P hb].
  move/(zlt_succ2P (ZS_pred xz) zz):ha;rewrite (BZsucc_pred xz) => hc; BZo_tac.
move: (BZor_tor) => tor.
split => //. 
  symmetry; apply: (or_succ_prop' tor pa).
symmetry; apply: (or_pred_prop' tor pb).
Qed.

Definition or_complete r := forall x, inc x (substrate r) ->
   (exists y, consecutive r x y) /\ (exists y, consecutive r y x).
Definition or_stable r E:= forall x, inc x E ->
   inc (or_succ r x) E /\ inc  (or_pred r x) E.
Definition or_connected r:= forall E, sub E (substrate r) -> or_stable r E ->
   E = emptyset \/ E = substrate r.
Definition or_likeZ r := [/\ total_order r, or_complete r & or_connected r].

Lemma BZ_order_props: or_likeZ BZ_order.
Proof.
move: BZor_tor => tor; split => //.
  move => x; rewrite BZor_sr; move /BZ_succ_pred => [sa sb _ _].
  by split; [ exists (BZsucc x) | exists (BZpred x)].
move => E; rewrite BZor_sr => EZ hE; case: (emptyset_dichot E) => xe; fprops.
right; apply: extensionality => //.
move: xe => [x xE].
apply: (BZ_ind1 (EZ _ xE) (p := fun t => inc t E) xE) => t ta tE.
  by move: (hE t tE) =>[ya yb]; move:(BZ_succ_pred (EZ _ tE)) => [_ _ <- _].
by move: (hE t tE) =>[ya yb]; move:(BZ_succ_pred (EZ _ tE)) => [_ _ _ <-].
Qed.

Lemma BZ_order_sfinc  f r' (r:= BZ_order) : 
   function_prop f BZ (substrate r') -> order r' ->
   (forall z, intp z -> glt r' (Vf f z) (Vf f (BZsucc z))) ->
   strict_increasing_fun f r r'.
Proof.
move => pa pd pe. 
move: BZor_sr (proj1 BZor_tor) => e1 or; rewrite - e1 in pa.
split => // x y /zlt_P ltxy.
have xz: intp x by BZo_tac.
have yz: intp y by BZo_tac.
move: y yz ltxy; apply: (BZ_ind1 xz);first by move => [].
  move => t ta HR _; move: (pe _ (proj32 ta)) => tb.
  case: (equal_or_not x t) => ext; first by rewrite ext.
  move: (HR (conj ta ext)) => tc; order_tac.
move => t ta _ tb; move: (zlt_leT tb (proj1 (zlt_pred (proj31 ta)))) => za.
BZo_tac.
Qed.

Lemma BZ_order_props_bis r: nonempty (substrate r) -> or_likeZ r ->
  r \Is BZ_order.
Proof.
move => [u uE] [pa pb pc]; apply: orderIS.
pose fp := induction_term (fun _ v => (or_succ r v)) u.
pose fn := induction_term (fun _ v => (or_pred r v)) u.
have ra: fp \0c = u by apply: (induction_term0).
have rb: fn \0c = u by apply: (induction_term0).
have rc: forall n, natp n -> fp (csucc n) = (or_succ r (fp n)).
   apply:induction_terms.
have rd: forall n, natp n -> fn (csucc n) = (or_pred r (fn n)).
   apply:induction_terms.
have re: forall n, natp n -> inc (fp n) (substrate r).
  apply: Nat_induction; [ ue | move => n nN Hrec].
  move: (proj1 (or_succ_prop pa (proj1 (pb _ Hrec)))); rewrite - (rc _ nN).
  move => aux; order_tac.
have rf: forall n, natp n -> inc (fn n) (substrate r).
  apply: Nat_induction; [ ue | move => n nN Hrec].
  move: (proj1 (or_pred_prop pa (proj2 (pb _ Hrec)))); rewrite - (rd _ nN).
  move => aux; order_tac.
have rg: forall n, natp n -> consecutive r (fp n) (fp (csucc n)).
  move => n nN; rewrite (rc _ nN); apply: (or_succ_prop pa).
  exact:(proj1 (pb _ (re _ nN))).
have rh: forall n, natp n -> consecutive r (fn (csucc n)) (fn n).
  move => n nN; rewrite (rd _ nN); apply: (or_pred_prop pa).
  exact:(proj2 (pb _ (rf _ nN))).
have spa: forall z, inc z BZp ->
  BZsucc z = BZ_of_nat (csucc (BZ_val z)).
  move => z zp; move: (BZps_sBZp ZpsS1)  CS0=> aa cs0.
  rewrite /BZsucc BZsumE /BZsum_v2 (Y_true (conj zp aa)).
  rewrite (Nsucc_rw (BZ_valN (BZp_sBZ zp))) //.
  by rewrite /BZ_one BZ_of_nat_val.
have spb: forall z, inc z BZms ->
  BZpred z = BZm_of_nat (csucc (BZ_val z)).
  move => z zp. 
  move: (BZ_di_neg_pos zp) (BZ_di_neg_pos ZmsS_m1) => ha hb.
  rewrite /BZpred /BZdiff BZopp_1 /BZ_mone BZsumE /BZsum_v2.
  have hc: ~(inc z BZp /\ inc (BZm_of_nat \1c) BZp) by case.
  rewrite (Y_false hc) (Y_true (conj ha hb)).
  by rewrite  BZm_of_nat_val (Nsucc_rw (BZ_valN (BZms_sBZ zp))).
pose fc x := Yo (Q x = C0) (fn (P x)) (fp (P x)).
set f := Lf fc BZ (substrate r).
have qa: forall z, intp z -> inc (fc z) (substrate r).
  move => z /BZ_valN h; rewrite /fc; Ytac hh; fprops. 
have ff: function f by apply: lf_function.
have sf: source f = BZ by rewrite /f; aw.
have tf: target f = substrate r by rewrite /f; aw.
have z0 := ZS0; have z1 := ZS1.
have spc: forall z, intp z -> consecutive r (Vf f z) (Vf f (BZsucc z)).
  move => z zz; move:(ZS_succ zz) => zz'; rewrite /f !LfV//.
  case /BZ_i0P: (zz) => zp; last first.
    rewrite (spa _ zp) /fc (BZp_sg zp) (BZ_of_nat_val) /BZ_of_nat; aw.
    Ytac0; Ytac0; exact: (rg _ (BZ_valN zz)).
  case: (equal_or_not z \1mz) => zm1.
    rewrite zm1 /BZsucc -{2} BZopp_1 (BZsum_opp_l ZS1) /fc. 
    rewrite (BZp_sg ZpS0) (BZms_sg ZmsS_m1); Ytac0; Ytac0.
    rewrite BZ_of_nat_val BZm_of_nat_val - succ_zero. 
    by move:(rh _ NS0); rewrite ra rb.
  have sbn: inc (BZsucc z) BZms.
    apply /zgt0xP; split; first by apply /zlt_succ2P => //; apply /zgt0xP.
    by dneg sa; rewrite - (BZpred_succ zz) sa /BZpred - BZopp_1 BZdiff_0l.
  rewrite /fc (BZms_sg zp) (BZms_sg  sbn); Ytac0; Ytac0.
  rewrite - {1} (BZpred_succ zz) (spb _ sbn) BZm_of_nat_val.
  exact: (rh _ (BZ_valN (BZms_sBZ sbn))).
move: (Imf_P ff); rewrite {1} sf => iP.
have qd: or_stable r (Imf f).
  move => x /iP [v vz ->]; split.
    rewrite - (or_succ_prop' pa (spc _ vz)); apply /iP.
    exists (BZsucc v) => //; apply: (ZS_succ vz).
  rewrite -(BZsucc_pred vz) -  (or_pred_prop' pa (spc _ (ZS_pred vz))). 
  apply /iP; exists (BZpred v) => //;apply: (ZS_pred vz).
move: (Imf_Starget ff); rewrite {2}/f; aw => qe.
case: (pc _ qe qd) => ip.
  by empty_tac1 (Vf f \0z); apply /iP; exists \0z.
move: (proj1 BZor_tor) (proj1 pa) => or1 or2.
have [_ _ _ sif]:strict_increasing_fun f BZ_order r.
  by apply:BZ_order_sfinc => // z /spc []. 
have bf: bijection_prop f (substrate BZ_order) (substrate r).
  hnf; rewrite BZor_sr sf - ip {2} /f; aw; split => //.
  split; last by apply: (surjective_pr1 ff); rewrite {2}/f; aw.
  by split => //; rewrite sf => a b af bf h; case: (zleT_ell af bf) => //;
       move /zlt_P /sif => []_; rewrite h.
exists f; split => //.
hnf; rewrite sf => a b az bz; split.
  move /zle_P => laz; case: (equal_or_not a b) => eq.
    rewrite eq; order_tac; Wtac.  
  by move /zlt_P: (conj laz eq) => /sif [].
move => h; apply /zle_P; case: (zleT_el az bz) => // /zlt_P /sif ha;order_tac.
Qed.


Lemma BZprod_Mlege0 a b c: inc c BZp -> a <=z b -> (a *z c)  <=z (b *z c).
Proof. 
move => cp ab; move: (ab) => [az bz _]; move: (BZp_sBZ cp) => cz.
move /(zle_diffP az bz): ab => p1.
apply/ (zle_diffP (ZSp az cz) (ZSp bz cz)). 
by rewrite - BZprodBl //;apply:ZpS_prod.
Qed.

Lemma BZprod_Mltgt0 a b c: inc c BZps -> a <z b -> (a *z c) <z (b *z c).
Proof. 
move => cp ab; move: (ab) => [[az bz _]_]; move: (BZps_sBZ cp) => cz.
move /(zlt_diffP az bz): ab => p1.
apply/(zlt_diffP (ZSp az cz) (ZSp bz cz)).
by rewrite - BZprodBl //;apply:ZpsS_prod.
Qed.

Lemma BZprod_Mlele0 a b c: inc c BZm -> a <=z b -> (b *z c)  <=z (a *z c).
Proof. 
move => cm; move: (BZopp_negative2 cm) => ocp ineq. 
move:  (BZprod_Mlege0 ocp (zle_opp ineq)).
move: ineq => [az bz _]; move: (BZm_sBZ cm) => cz.
rewrite BZprod_opp_opp // BZprod_opp_opp //.
Qed.

Lemma BZprod_Mltlt0 a b c: inc c BZms -> a <z b -> (b *z c) <z (a *z c).
Proof. 
move => cm; move: (BZopp_negative1 cm) => ocp ineq. 
move:  (BZprod_Mltgt0 ocp (zlt_opp ineq)).
move: ineq => [[az bz _] _]; move: (BZms_sBZ cm) => cz.
rewrite BZprod_opp_opp // BZprod_opp_opp //.
Qed.


Lemma BZ1_small c: inc c BZps -> \1z <=z c.
Proof.
move => h; move: (BZps_sBZ h) ZS1 => pa pb; split => //; constructor 3.
move /indexed_P:h => [_ /setC1_P [pc pd] etc].
rewrite /BZ_one /BZ_of_nat /int_pp; aw; split => //;  apply cge1; fprops.
Qed.

Lemma BZprod_Mpp  b c: inc b BZp ->  inc c BZps -> b <=z (b *z c).
Proof.
move => pa pb; move:(BZp_sBZ pa) => bb.
by move: (BZprod_Mlege0 pa (BZ1_small pb)); rewrite (BZprodC c) BZprod_1l.
Qed.


Lemma BZprod_Mlepp a b c: inc b BZp -> inc c BZps -> a <=z b -> a <=z (b *z c).
Proof. 
move => pa pb pc; move: (BZprod_Mpp  pa pb) => pd;  BZo_tac.
Qed.

Lemma BZprod_Mltpp a b c: inc b BZp -> inc c BZps -> a <z b -> a <z (b *z c).
Proof. 
move => pa pb pc; move: (BZprod_Mpp  pa pb) => pd;  BZo_tac.
Qed.

Lemma BZprod_Mlelege0 a b c d: inc b BZp -> inc c BZp ->
  a <=z b -> c <=z  d -> (a *z c)  <=z (b *z d).
Proof. 
move => pa pb pc pd.
move: (BZprod_Mlege0 pb pc) (BZprod_Mlege0 pa pd) => r1.
rewrite  (BZprodC c) (BZprodC d) => r2; BZo_tac.
Qed.

Lemma BZprod_Mltltgt0 a b c d: inc b BZps -> inc c BZps ->
  a <z b -> c <z  d -> (a *z c)  <z (b *z d).
Proof. 
move => pa pb pc pd.
move: (BZprod_Mltgt0 pb pc) (BZprod_Mltgt0 pa pd) => r1.
rewrite  (BZprodC c) (BZprodC d) => r2; BZo_tac.
Qed.

Lemma BZprod_Mltltge0 a b c d: inc a BZp -> inc c BZp ->
  a <z b -> c <z  d -> (a *z c)  <z (b *z d).
Proof. 
move => pa pb pc pd.
have H: (forall a b, inc a BZp ->  a <z b -> inc b BZps).
  move => u v up uv; move: (uv) => [[uz vz _] _].
  move/ (zlt_diffP uz vz): uv => pe; move: (ZpsS_sum_r up pe).
  by rewrite BZsum_diff.
move: (H _ _ pa pc) (H _ _ pb pd) => bp cp.
case: (equal_or_not c \0z) => cnz.
  by rewrite cnz BZprod_0r; apply /zlt0xP; apply: ZpsS_prod.
by apply: BZprod_Mltltgt0 => //; apply/ BZps_iP;split.
Qed.

Lemma BZprod_ple2r a b c: intp a -> intp b -> inc c BZps ->
   ((a *z c)  <=z (b *z c) <-> a <=z b).
Proof.
move => pa pb pc; move: (BZps_sBZp pc)=> p'c.
split; last by apply:BZprod_Mlege0.
move => h; case: (zleT_el pa pb) => // h1.
move: (BZprod_Mltgt0 pc h1) => h2; BZo_tac.
Qed.

Lemma BZprod_plt2r a b c: intp a -> intp b ->  inc c BZps ->
  ((a *z c)  <z (b *z c) <-> a <z b).
Proof.
move => pa pb pc; move: (BZps_sBZp pc)=> p'c.
split; last by  apply:BZprod_Mltgt0.
move => h; case: (zleT_el pb pa) => //.
move /(BZprod_ple2r pb pa pc) => h2; BZo_tac.
Qed.


(** ** Division *)


Definition BZdivision_prop a b q r := 
  [/\ a = (b *z q) +z r, r <z (BZabs b) & inc r BZp].

Definition BZquo_int a b :=
  let  q:= BZ_of_nat ((BZ_val a) %/c (BZ_val b)) in 
    Yo (b = \0z) \0z
    (Yo (int_pp a) (Yo (int_pp b) q (BZopp q))
      (Yo ((BZ_val a %%c BZ_val b) = \0c)  (Yo (int_pp b) (BZopp q) q)
        (Yo (int_pp b) (BZopp (BZsucc q)) (BZsucc q)))).

Definition BZquo := locked BZquo_int.
Notation "x %/z y" := (BZquo x y) (at level 40).

Definition BZrem a b := a -z b *z (a %/z b).
Notation "x %%z y" := (BZrem x y) (at level 40).



Lemma BZquo_val a b (q1:= ((BZ_val a) %/c (BZ_val b))) (q2 := BZ_of_nat q1):
   intp a -> intp b -> [/\ inc q1 Nat, inc q2 BZp & inc q2 BZ].
Proof.   
move => az bz. 
move: (NS_quo (P b) (BZ_valN az)) => qb.
by move: (BZ_of_natp_i qb) => pa; move: (BZp_sBZ pa) => pb. 
Qed.

Lemma BZ_quo0 a: a %/z \0z = \0z.
Proof. by rewrite /BZquo - lock /BZquo_int ; Ytac0. Qed.

Lemma BZ_quorem0 a: intp a -> (a %%z \0z = a /\ a %/z \0z = \0z). 
Proof.
move => pa; move:(BZ_quo0 a) => pb.
by split => //; rewrite /BZrem pb /BZdiff BZprod_0r BZopp_0 BZsum_0r.
Qed.

Lemma BZ_quorem00 b: intp b -> (\0z %%z b = \0z /\ \0z %/z b = \0z). 
Proof.
move => bz.
case: (equal_or_not b \0z); first by  move => ->; apply: (BZ_quorem0 ZS0).
move: ZS0 => zz bnz.
have: \0z %/z b = \0z.  
  rewrite /BZquo - lock / BZquo_int; Ytac0; rewrite BZ0_val.
  move: (cdivision_of_zero (BZ_valN bz)) => [[qa qb ->] ->]. 
  by rewrite -/BZ_zero BZopp_0; Ytac0; Ytac0; Ytac0.
move => h;split => //; rewrite /BZrem h BZprod_0r; apply: (BZdiff_diag zz).
Qed.

Lemma ZS_quo a b: intp a -> intp b  -> intp (a %/z b).
Proof. 
move => az bz; rewrite /BZquo - lock /BZquo_int.
move: (BZquo_val az bz) => [_ _]; set q := BZ_of_nat _ => qz.
move: (ZSo qz) (ZS_succ qz) ZS0=> oqz sqz z0.
by Ytac ra => //; Ytac rb; Ytac rc => //; Ytac rd => //; apply:ZSo.
Qed.

Lemma ZpS_quo a b: inc a BZp -> inc b BZp -> inc (a %/z b) BZp.
Proof. 
move => az bz.
move: (BZquo_val  (BZp_sBZ az) (BZp_sBZ bz)) => [_]. 
set q := BZ_of_nat _ => qz _.
rewrite /BZquo - lock /BZquo_int; Ytac ra; first by apply: ZpS0.
by rewrite /int_pp (BZp_sg az) (BZp_sg bz);Ytac0; Ytac0.
Qed.

Lemma ZS_rem a b: intp a -> intp b -> intp (a %%z b).
Proof. 
by move => pa pb; move: (ZS_quo pa pb) => pc; apply: ZS_diff=> //; apply: ZSp.
Qed.

Lemma BZquo_opp_b a b: intp a -> intp b -> a %/z (BZopp b) = BZopp (a %/z b).
Proof.
move => az bz.
case: (equal_or_not b \0z) => bn0.
  by rewrite bn0 BZopp_0  BZ_quo0  BZopp_0.
have bon0: BZopp b <> \0z by dneg xx; move: (BZopp_K bz); rewrite xx BZopp_0.
rewrite /BZquo - lock /BZquo_int; Ytac0; Ytac0; rewrite BZopp_val.
move: (BZquo_val az bz) => [_ _]; set q := BZ_of_nat _ => qzp.
move: (BZopp_sg bz bn0) => [aux1 aux2].
case: (equal_or_not (Q b) C0) => ha. 
  rewrite/int_pp  (aux1 ha) ha; Ytac0; Ytac0; Ytac0; Ytac0; Ytac0; Ytac0.
  by Ytac hb; Ytac0;  [symmetry;apply: BZopp_K |  Ytac hc; Ytac0].
case: (BZ_sgv bz); [ by done | move => bp].
rewrite /int_pp (aux2 bp); do 6 Ytac0; Ytac pc; Ytac0 => //. 
by Ytac pd; Ytac0 => //;rewrite BZopp_K //;  apply: ZS_succ.
Qed.

Lemma BZrem_opp_b a b: intp a -> intp b -> a %%z (BZopp b) = a %%z b.
Proof.
move => az bz; rewrite /BZrem  (BZquo_opp_b az bz).
by rewrite  (BZprod_opp_opp bz (ZS_quo az bz)).
Qed.


Lemma BZquo_div1 a b: intp a -> intp b -> b <> \0z -> 
   (BZ_val a) %%c (BZ_val b) = \0c -> a = b *z  (a %/z b).
Proof.
move => az bz bnz de; rewrite /BZquo - lock /BZquo_int; Ytac0; Ytac0.
move: (BZquo_val az bz) => [_ ]; set q := BZ_of_nat _ => [qzp qz].
have pbz: P b <> \0c by move => h; case: bnz;  exact (BZ_0_if_val0 bz h). 
move:  (cdivision(BZ_valN az) (BZ_valN bz) pbz)=> [_ _ [aa _]].
have aux: cardinalp (P b *c (P a %/c P b)) by  fprops.
have Pa: P a =  P b *c P q.   
   by rewrite  BZ_of_nat_val; move: aa; rewrite de csum0r.
case: (BZ_sgv az) => sa; rewrite /int_pp sa; Ytac0.
  rewrite -(proj2 (BZms_hi_pr (BZms_i az sa))) Pa;case: (BZ_sgv bz) => sb.
     by rewrite  sb; Ytac0; rewrite (BZprod_mp  (BZms_i bz sb) qzp).
  Ytac0; rewrite (BZprod_opp_comm bz qz).
  have bps: inc b BZps by apply /BZps_iP; split => //; exact (BZp_i bz sb).
  by rewrite (BZprod_mp (BZopp_positive1 bps) qzp) BZopp_val.
rewrite - (BZp_hi_pr (BZp_i az sa)) Pa;case:(BZ_sgv bz) => sb; rewrite sb;Ytac0.
  move: (BZps_sBZp (BZopp_negative1 (BZms_i bz sb))) => h.
  by rewrite (BZprod_opp_comm bz qz) (BZprod_pp h qzp) BZopp_val.
by rewrite -(BZprod_pp (BZp_i bz sb) qzp).
Qed.

Lemma BZrem_div1 a b: intp a -> intp b -> b <> \0z -> 
   (BZ_val a) %%c (BZ_val b) = \0c -> (a %%z b) = \0z.
Proof.
move => az bz bnz de; rewrite /BZrem  {1} (BZquo_div1 az bz bnz de).
exact: (BZdiff_diag (ZSp bz (ZS_quo az bz))).
Qed.

Lemma BZquo_opp_a1 a b: intp a -> intp b -> b <> \0z ->
   (BZ_val a) %%c (BZ_val b) = \0c -> (BZopp a) %/z b = BZopp (a %/z b).
Proof.
move => az bz bnz de.
move: (BZquo_div1 az bz bnz de) => r1.
move: de; rewrite -(BZopp_val a) => de.
move: (ZS_quo az bz) (ZSo az) => qz naz.
move: (BZquo_div1 naz bz bnz de); rewrite  {1} r1.
rewrite (BZopp_prod_r bz qz) => e1.
symmetry;apply: (BZprod_eq2l (ZSo qz)  (ZS_quo naz bz)  bz bnz e1). 
Qed.


Lemma BZdivision_opp_a2 a b:
   intp a -> intp b -> b <> \0z -> (P a %%c P b) <> \0c ->
  ( (BZopp a) %%z b <> \0z
   /\ (BZopp a) %%z b =  (BZabs b) -z (a %%z b)).
Proof.
move =>  az bz bnz pz; split.
    set c := BZopp a; move:(ZSo az) => cz.
    rewrite /BZrem => ez. 
    have ha: inc (BZopp a %/z b) BZ by apply: ZS_quo.
    move /(BZdiff_diag_rw cz (ZSp bz (ZS_quo cz bz))): ez => h.
    move: (f_equal P h); rewrite BZopp_val (BZprod_abs2 bz ha); aw.
    move: (BZ_valN ha); set q := P _ => qB eq.
    by move: (cdivides_pr1 qB (BZ_valN bz)) => [_ _]; rewrite - eq.
set c := BZabs b.
suff: BZopp a %%z c = c -z a %%z c.
  move => t; case /BZ_i0P: (bz) => bs; last by rewrite - (BZabs_pos bs).
  by rewrite - (BZrem_opp_b az bz) -( BZrem_opp_b (ZSo az) bz)- (BZabs_neg bs).
rewrite /BZrem; set q := (a %/z c).
suff: BZopp a %/z c = BZopp (BZsucc q).
  have bza: intp c by apply: ZSa.
  have qz: intp q by apply: ZS_quo.
  have sq1 := (ZSs qz ZS1).
  move: (ZSp bza qz) => sq2.
  move => ->.
  rewrite /BZsucc /BZdiff (BZopp_prod_r bza (ZSo sq1)) (BZopp_K sq1).
  rewrite (BZoppB az sq2) BZsumC (BZsumA bza sq2 (ZSo az)).
  by rewrite (BZprodDr bza qz ZS1) (BZprod_1r bza) (BZsumC c).
case: (equal_or_not a \0z) => anz.
   case: pz; rewrite anz BZ0_val.
   by move: (cdivision_of_zero (BZ_valN bz)) => [ [_ _ ok] _].
have panz: (P a <> \0c) by  move =>h;  case: anz;  exact (BZ_0_if_val0 az h). 
have cnz: c <> \0z by move => cz; move:(BZabs_0p bz cz).
rewrite /q /BZquo -lock /BZquo_int/int_pp (BZabs_sg bz)(BZabs_val b) BZopp_val.
set q1:= (BZ_of_nat _).
have q1z: intp q1 by apply: BZ_of_nat_i;apply: NS_quo;apply: BZ_valN.
move: (ZS_succ q1z) => q2z; move: (ZSo q2z) => q3z.
move: (BZabs_sg bz) => hh.
do 5 Ytac0.
rewrite {1} /BZopp.
rewrite /int_pp/int_np; case: (equal_or_not (Q a) C0).
  move => ->; Ytac0; Ytac0; rewrite /BZ_of_nat; aw; Ytac0.
  rewrite (BZoppD q3z ZS1) (BZopp_K q2z).
  rewrite /BZsucc (BZsumC q1) - {1} (BZdiff_sum ZS1 q1z) //.
move => qna; case: (BZ_sgv az) => qaa; first by case: qna.
by Ytac0; Ytac0; rewrite /BZm_of_nat; Ytac0; aw; Ytac0.
Qed.


Lemma BZdvd_correct a b: intp a -> intp b -> b <> \0z ->
  [/\ inc (a %/z b) BZ, inc (a %%z b) BZp &
  (BZdivision_prop a b (a %/z b) (a %%z b))].
Proof.
move => az bz bnz.
pose aux a b := a %%z b <z BZabs b /\ inc (a %%z b) BZp.
suff: aux a b. 
  move: (ZS_quo az bz) => qz [pa pb]; split => //; split => //.
  by rewrite /BZrem (BZsum_diff (ZSp bz qz) az).
have Ha: forall a b,  inc a BZp -> inc b BZps -> aux a b.
  move => u v up /BZps_iP [vp vnz].
  rewrite /aux (BZabs_pos vp) /BZrem.
  move: (BZp_sBZ vp)  (BZp_sBZ up) => vz uz.
  set q := (u %/z v).
  suff: (u <z v *z (q +z \1z) /\ v *z q <=z u).
    move => [pa pb].
    move: (proj31 pb) => pz.
    move:(ZS_diff (proj32 pb) pz) => rz.
    split; last by apply /(zle_diffP pz uz).
    apply /(BZsum_lt2r rz vz pz); rewrite BZsumC (BZsum_diff pz uz).
    by move: pa; rewrite (BZprodDr vz (ZS_quo uz vz) ZS1) BZsumC BZprod_1r.
  have: q =  u %/z v by done.
  rewrite /BZquo - lock /BZquo_int (Y_true (BZp_sg up)) (Y_true (BZp_sg vp)).
  rewrite (Y_false vnz) => ->.
  move: (BZ_valN (BZp_sBZ up)) (BZ_valN (BZp_sBZ vp)) => pa pb.
  have pc: P v <> \0c by move => h; case: vnz;  exact (BZ_0_if_val0 vz h). 
  move: (cdivision pa pb pc).
  clear q; set q := (P u %/c P v); set r  := (P u %%c P v).
  move => [qB rB [dp mp]]; move: (BZ_of_natp_i qB) => qzb.
  move /BZps_iP: ZpsS1 => [bz1p _].
  split.
    rewrite (BZsum_pp qzb bz1p) /BZ_one !BZ_of_nat_val.
    rewrite (BZprod_pp vp (BZ_of_natp_i (NS_sum qB NS1))) BZ_of_nat_val.
    apply /(zlt_P1 up). 
        by apply: BZ_of_natp_i;rewrite -/(natp _); fprops.
    rewrite BZ_of_nat_val dp cprodDr (cprod1r (CS_nat pb)).
    rewrite csumC (csumC _ (P v)); exact:(csum_Mlteq (NS_prod pb qB) mp).
  have ppb: inc (P v *c q) Nat by apply:NS_prod.
  rewrite (BZprod_pp vp (BZ_of_natp_i qB)) BZ_of_nat_val.
  apply /(zle_P1 _ up); first by apply: BZ_of_natp_i.
  by rewrite BZ_of_nat_val dp; apply:(Nsum_M0le _ ppb).
have Hb: forall a b,  inc a BZp -> intp b ->  b <> \0z -> aux a b.
   move => u v => up vp vnz.
   case /BZ_i1P: vp; [by done | by move => h; apply: Ha | ].
   move => vm; move: (BZopp_negative1 vm) => ovp.
   move: (BZrem_opp_b (BZp_sBZ up) (BZms_sBZ vm)) => e1.
   by move: (Ha _ _ up ovp); rewrite /aux e1 BZabs_opp.
case /BZ_i0P: (az); last by move => h;apply: Hb.
move => ams;  move: (BZopp_negative1 ams) => oap.
move: (Hb _ _ (BZps_sBZp oap) bz bnz) => [pa pb].
case: (equal_or_not ((P a) %%c (P b)) \0c) => de.
  move: (BZrem_div1 az bz bnz de) => rz.
  rewrite /aux rz;split ; [ exact : (BZabs_positive bz bnz) | apply: ZpS0 ].
move: (BZdivision_opp_a2 az bz bnz de) => [r2 r1].
move: pa pb r2; rewrite /aux r1; set X := _ %%z _; set bb :=  BZabs b.
have Xp: inc X BZ by apply: ZS_rem.
move: (ZSa bz) => abz.
move => pa pb pc; split.
  apply /(zlt_diffP Xp abz); apply /BZps_iP; split => // => e1.
move /(zlt_diffP  (ZS_diff abz Xp) abz) : pa.
by rewrite /BZdiff BZoppB // BZsum_diff //; move /BZps_iP => [].
Qed.

Lemma ZpS_rem a b: intp a -> intp b -> b <> \0z -> inc (a %%z b) BZp.
Proof. 
by move => pa pb pc;move: (BZdvd_correct pa pb pc) => [_ ok _].
Qed.

Lemma BZrem_small a b:  intp a -> intp b -> b <> \0z -> 
   (a %%z b) <z (BZabs b).
Proof.
by move => pa pb pc;move: (BZdvd_correct pa pb pc) => [_ _ [ _ bb _]].
Qed.

Lemma BZdvd_exact b q: intp q -> intp b -> b <> \0z ->
  ((q *z b) %/z b = q /\  (q *z b) %%z b = \0z).
Proof.
move => qz bz bnz; move: (ZSp qz bz);set a := (q *z b) => az.
have aux:  (P a) %%c (P b) = \0c.
  move: (cdivides_pr1 (BZ_valN qz) (BZ_valN bz)) => [_ _].
  by rewrite BZprod_val cprodC.
split; last by rewrite (BZrem_div1 az bz bnz aux).
move: (BZquo_div1 az bz bnz aux); rewrite {1} /a BZprodC => h.
symmetry; exact (BZprod_eq2l qz (ZS_quo az bz) bz bnz h).
Qed.

Lemma BZdvd_unique a b q r q' r': intp a -> intp b -> b <> \0z ->
  intp q -> intp r -> intp q' -> intp r' -> 
  BZdivision_prop a b q r -> BZdivision_prop a b q' r' ->
  (q = q' /\ r =r').
Proof. 
move => az bz qnz; move: q r q' r'.
have alt:forall q r,  inc q BZ -> inc r BZ -> BZdivision_prop a b q r ->
  [/\ (b *z q) <=z a,  a <z (b *z ((BZsign b) +z q)) & r = a -z (b  *z q)].
  move => q r qz rz.
  move: (ZSp bz qz) (ZS_sign b) => qa qb.
  have qc: b *z (BZsign b +z q) = b *z q +z BZabs b.
    by rewrite (BZprodDr bz qb qz) BZsumC (BZsign_abs bz).
  move: (BZsum_lt2l rz (ZSa bz) qa) => qd.
  move => [pa pb pc];split => //. 
       by rewrite pa; apply: BZsum_Mp.
    by rewrite qc pa; apply /qd.
   by rewrite pa BZdiff_sum.
move => q r q' r' qz rz q'z r'z h h'.
move: (alt _ _ qz rz h) => [pa pb pc].
move: (alt _ _ q'z r'z h') => [pa' pb' pc'].
suff: q = q' by move => sq;  rewrite pc pc' sq.
move: (ZS_sign b) => ab.
have aux: forall q q', inc q BZ -> inc q' BZ ->
   b *z q' <z b *z (BZsign b +z q) -> inc (b *z (BZsign b +z (q -z q'))) BZps.
  move => z z' zz z'z le.
  move:  (ZSs ab zz) => sa.
  move /(zlt_diffP (ZSp bz z'z) (ZSp bz sa)): le.
  by rewrite - (BZprodBr bz sa z'z) /BZdiff (BZsumA ab zz (ZSo z'z)).
have aux2: forall q q', inc q BZ -> inc q' BZ -> 
    inc (\1z +z (q -z q')) BZps -> q' <=z q.
  move => z z' zz z'z le;apply /(zlt_succ1P z'z zz).
  apply /(zlt_diffP z'z (ZS_succ zz)). 
  by rewrite  /BZsucc /BZdiff (BZsumC z) - (BZsumA ZS1 zz (ZSo z'z)). 
have aux3: forall q q', inc q BZ -> inc q' BZ -> 
    inc (\1mz +z (q -z q')) BZms -> q <=z q'.
  move => z z' zz z'z le; move: (BZopp_negative1 le).
  rewrite (BZoppD ZSm1 (ZS_diff zz z'z)).
  by rewrite (BZoppB zz z'z) BZopp_m1; apply: aux2.
have r1:  b *z q <z b *z (BZsign b +z q') by BZo_tac.
have r2:  b *z q' <z b *z (BZsign b +z q) by BZo_tac.
move: (aux _ _ qz q'z r2) (aux _ _ q'z qz r1) => r3 r4.
move: (BZps_stable_prod1 bz (ZSs ab (ZS_diff qz q'z)) r3).
move: (BZps_stable_prod1 bz (ZSs ab (ZS_diff q'z qz)) r4).
case /BZ_i1P: bz => ha //.
  move=> [s1 s2] [s3 s4].
  move/s1: (ha); move/s3: (ha); rewrite (BZsign_pos ha) => s5 s6.
  move: (aux2 _ _ qz q'z s5) (aux2 _ _ q'z qz s6) => l1 l2; BZo_tac.
move=> [s1 s2] [s3 s4].
move/s2: (ha); move/s4: (ha); rewrite (BZsign_neg ha) => s5 s6.
move: (aux3 _ _ qz q'z s5) (aux3 _ _ q'z qz s6) => l1 l2; BZo_tac.
Qed.

Lemma BZdvd_unique1 a b q r: intp a -> intp b ->
  intp q -> intp r -> b <> \0z ->
  BZdivision_prop a b q r -> (q = a %/z b /\ r  = a %%z b).
Proof. 
move => pa pb pc pd pe H1.
move:  (BZdvd_correct pa pb pe) => [pc' pd'' H2]. 
exact (BZdvd_unique pa pb pe pc pd pc' (BZp_sBZ pd'')  H1 H2).
Qed.

Lemma BZquo_cN a b: natp a -> natp b -> 
  (BZ_of_nat a) %/z  (BZ_of_nat b) =  BZ_of_nat (a%/c b).
Proof.
move => aN bN.
rewrite /BZquo - lock /BZquo_int /BZ_of_nat /int_pp  !pr1_pair !pr2_pair.
by Ytac0; Ytac0;Ytac h => //; rewrite(pr1_def h) cquo_zero.
Qed.

Lemma BZrem_cN a b: natp a -> natp b -> 
  (BZ_of_nat a) %%z  (BZ_of_nat b) =  BZ_of_nat (a%%c b).
Proof.
move => aN bN.
move: (BZ_of_nat_i aN) => az.
move: (BZ_of_nat_i bN) => bz.
case: (equal_or_not b \0c) => bc.
  by rewrite bc (crem_zero aN) (proj1 (BZ_quorem0 az)).
have bbnz: (BZ_of_nat b) <> \0z by move/pr1_def.
move:(BZdvd_correct az bz bbnz) => [ _ _ [h _ _]].
move: (cdivision aN bN bc) => [sa sb [sc sd]].
move: (BZ_of_nat_i (NS_prod bN sa))(BZ_of_nat_i sb) => ha hb.
move: h; rewrite (BZquo_cN aN bN) {1} sc - (BZsum_cN (NS_prod bN sa) sb).
by rewrite (BZprod_cN bN sa); move/(BZsum_eq2l ha hb (ZS_rem az bz)).
Qed.


(** ** Divisiblity *)

Definition BZdivides b a := 
  [/\ intp a, intp b & BZrem a b = \0z].

Notation "x %|z y" := (BZdivides x y) (at level 40).


Lemma BZdvds_pr a b: b %|z a -> a = b *z  (a %/z b).
Proof. 
move => [pa pb pd]. 
move: pd; rewrite /BZrem => h.
exact  (BZdiff_diag_rw pa (ZSp pb (ZS_quo pa pb)) h).
Qed.

Lemma BZdvds_trivial: \0z %|z \0z.
Proof. have z0:= ZS0;split => //; exact:(proj1 (BZ_quorem0 ZS0)). Qed.


Lemma BZdvds_trivial_rec x: \0z %|z x -> x = \0z.
Proof. by move => [/BZ_quorem0 [sa _] _ ]; rewrite sa. Qed.


Lemma BZdvds_pr1 a b: intp a -> intp b -> b %|z (a *z b).
Proof.
move => pa pb; case: (equal_or_not b \0z) => H.
    rewrite H BZprod_0r; apply:BZdvds_trivial.
by move:(BZdvd_exact pa pb H) => [_ dd]; split => //;apply: ZSp.
Qed.

Lemma BZdvds_pr1' a b: intp a -> intp b ->  b %|z (b *z a).
Proof.  by move => pa pb ; rewrite BZprodC; apply:BZdvds_pr1. Qed.

Lemma BZdvd_pr2 a b q: inc q BZ -> intp b -> b <> \0z -> 
  a = b *z q -> q = a %/z b. 
Proof. 
move => qz bz bnz pd.
move: (ZSp bz qz); rewrite - pd => az.
have hh: (BZdivision_prop a b q \0z).
   red; rewrite - pd (BZsum_0r az);split => //; last by apply: ZpS0.
   split; last by move => abz; case: bnz;apply: (BZabs_0p bz).
   apply /zle0xP; exact (BZabs_iN bz). 
exact (proj1 (BZdvd_unique1 az bz qz ZS0 bnz hh)).
Qed.

Lemma BZdvds_pr0 a b: b %|z a ->  (BZ_val b) %|c (BZ_val a).
Proof. 
move => [az bz etc].
move: (BZdiff_diag_rw az (ZSp bz (ZS_quo az bz)) etc).
move => h; move: (f_equal P h); rewrite BZprod_val => ->.
by apply: cdivides_pr1; apply: BZ_valN => //;apply:ZS_quo.
Qed.

Lemma BZdvds_pr3 a b: intp a -> intp b ->
  (b %|z a <->  (BZ_val b) %|c  (BZ_val a)).
Proof. 
move => az bz.
split; [ by apply:BZdvds_pr0 | move => [sa sb sc] ].
case: (equal_or_not b \0z) => bnz. 
   suff: a = \0z by  move -> ; rewrite bnz;apply:BZdvds_trivial.
   by apply: (BZ_0_if_val0 az); rewrite - sc bnz BZ0_val (crem_zero sa).
split => //; exact:(BZrem_div1 az bz bnz sc).
Qed.

Lemma BZdiv_cN a b: natp a -> natp b ->
   ((a %|c b) <-> (BZ_of_nat a) %|z (BZ_of_nat b)).
Proof.
move => aN bN; apply: iff_sym.
move:(BZdvds_pr3 (BZ_of_nat_i bN) (BZ_of_nat_i aN)).
by rewrite !BZ_of_nat_val.
Qed.


Lemma BZdvds_opp1 a b: intp b ->
  (b %|z a <->  (BZopp b) %|z a).
Proof. 
move => bz; move: (ZSo bz) => obz. 
split;move=> [pa pb pc]; hnf.
 by  rewrite /BZdivides (BZrem_opp_b pa pb).
by rewrite -(BZrem_opp_b pa bz) pc.
Qed.

Lemma BZdvds_opp2 a b: intp a ->  (b  %|z a  <-> b %|z (BZopp a)).
Proof. 
move => az; move: (ZSo az) => oaz.
split; move => h; move: (BZdvds_pr0 h) => h1;move: h=> [pa pb pc].
  by apply/(BZdvds_pr3 oaz pb);  rewrite BZopp_val.
by apply /(BZdvds_pr3 az pb);  rewrite -(BZopp_val a).
Qed.

Lemma BZquo_opp2 a b: b  %|z a -> (BZopp a) %/z b = BZopp (a %/z b).
Proof. 
move => h; move: (BZdvds_pr0 h) => [_ _ h1]; move: h => [az pb pc].
case: (equal_or_not b \0z) => bnz; first by rewrite bnz !BZ_quo0 BZopp_0.
by apply: BZquo_opp_a1.
Qed.

Lemma BZdvds_one a: intp a -> \1z %|z a.
Proof. by move=> az; move: (BZdvds_pr1 az ZS1); rewrite BZprod_1r. Qed.

Lemma BZdvds_mone a: intp a -> \1mz %|z a.
Proof. 
by move=> az;rewrite - BZopp_1;  move/(BZdvds_opp1 a ZS1) : (BZdvds_one az).
Qed.

Lemma BZquo_one a: intp a -> a %/z \1z = a.
Proof. 
by move => az; symmetry; apply:(BZdvd_pr2 az ZS1 BZ1_nz); rewrite BZprod_1l. 
Qed.

Lemma BZquo_mone a: intp a -> a %/z \1mz = BZopp a.
Proof.
move=> az;rewrite - BZopp_1 - {2} (BZquo_one az); apply:(BZquo_opp_b az ZS1).
Qed.

Lemma BZdvds_pr4 a b q: b %|z a -> q = a %/z b -> a = b *z q.
Proof. by move => H ->;exact: (BZdvds_pr H). Qed.

Lemma BZdvds_pr5 b q:  intp b -> inc q BZ -> b <> \0z ->  (b *z q) %/z b = q.
Proof. by move=> pa pb pc; symmetry; apply:BZdvd_pr2. Qed.

Lemma BZdvd_itself a: intp a -> a <> \0z ->  (a %|z a /\ a %/z a = \1z).
Proof. 
move => az anz.
move: (BZdvds_pr1 ZS1 az) (BZdvds_pr5 az ZS1 anz). 
by rewrite (BZprod_1r az) (BZprod_1l az).
Qed.

Lemma BZdvd_opp a: intp a -> a <> \0z ->  
   (a %|z (BZopp a) /\  (BZopp a)  %/z a = \1mz).
Proof. 
move => az anz;move: (BZdvd_itself az anz) => [pa pb].
rewrite (BZquo_opp2 pa) pb BZopp_1.
split; [ by move/ (BZdvds_opp2 a az): pa | done].
Qed.


Lemma BZdvd_zero1 a: intp a -> (a %|z \0z /\ \0z %/z a = \0z).
Proof. 
move => az; move: (BZ_quorem00 az) => [pa pb]. 
split => //; split => //; apply: ZS0.
Qed.

Lemma BZdvds_trans a b a': a %|z a'-> b %|z a ->  b %|z  a'.
Proof. 
move => pa pb.
rewrite  (BZdvds_pr pa) {1} (BZdvds_pr pb).
move: pa pb => [a'z az _] [_  bz _].
move:  (ZS_quo az bz)(ZS_quo a'z az) => qa qb.
rewrite - (BZprodA bz qa qb)  BZprodC.
by apply: (BZdvds_pr1 (ZSp qa qb) bz). 
Qed.

Lemma BZdvds_trans1 a b a': a %|z a'-> b %|z a -> 
    a' %/z b = (a' %/z a) *z (a %/z b).
Proof.
move => pa pb.
rewrite {1} (BZdvds_pr pa) {1} (BZdvds_pr pb).
move: pa pb => [a'z az _ ] [_ bz _]. 
case: (equal_or_not b \0z) => bnz; first by rewrite bnz !BZ_quo0 BZprod_0r.
move:  (ZS_quo az bz)(ZS_quo a'z az) => qa qb.
by rewrite - (BZprodA bz qa qb) (BZdvds_pr5 bz (ZSp qa qb) bnz) BZprodC.
Qed.

Lemma BZdvds_trans2 a b c: intp c -> b %|z a -> b %|z (c *z a).
Proof.
move => cz dv1; move: (dv1)=> [h _ _ ].
exact:  (BZdvds_trans  (BZdvds_pr1 cz h) dv1).
Qed.

Lemma BZquo_simplify a b c: intp a -> intp b -> inc c BZps ->
   ( (a *z c) %/z(b *z c) = a %/z b /\
     (a *z c) %%z (b *z c) =  (a %%z b) *z c).
Proof. 
move => az bz czp.
case (equal_or_not b \0z) => bnz.
   rewrite bnz BZprod_0l //.
   move:  (BZ_quorem0 az) => [-> ->].
   by move: (BZ_quorem0 (ZSp az (BZps_sBZ czp))) => [-> ->].
move:(BZdvd_correct az bz bnz); set q := a %/z b; set r := (a %%z b).
move => [qz rzp [qr r0 r1]].
move: (BZps_sBZ czp)(BZp_sBZ rzp) => cz rz.
move /BZps_iP: (czp) => [pa pb].
move: (ZpS_prod rzp pa) => pc.
have pd: a *z c = (b *z c) *z q +z r *z c.
  rewrite qr (BZprodDl cz (ZSp bz qz) rz).
  by rewrite BZprodC (BZprodA  cz bz qz) (BZprodC c).
have pe: r *z c <z BZabs (b *z c).
  rewrite (BZprod_abs bz cz) (BZabs_pos pa).
  by apply /(BZprod_plt2r rz (ZSa bz) czp).
have bcnz: (b *z c) <> \0z.
   by apply: BZprod_nz => //;move /BZps_iP: czp => [_].
have h: (BZdivision_prop (a *z c) (b *z c)  q (r *z c)) by split => //.
move: (BZdvd_unique1 (ZSp az cz) (ZSp bz cz) qz (ZSp rz cz) bcnz h). 
by move => [-> ->].
Qed.

Lemma BZdvds_prod a b c: intp a -> intp b -> intp c -> c <> \0z ->
   ( a %|z b <->  (a *z c) %|z (b *z c)). 
Proof.
move => az bz cz cnz.
move: (ZS_quo bz az) => baz.
split => h.
  rewrite (BZdvds_pr h) (BZprodC a (b %/z a)) -(BZprodA baz az cz).
  apply:(BZdvds_pr1 baz (ZSp az cz)); apply: BZprod_nz => //.
move: (BZdvds_pr h).  
move: (ZS_quo (ZSp bz cz)(ZSp az cz)).
set t := (b *z c) %/z (a *z c) => tz.
rewrite (BZprodC a)  (BZprodC _ c) - (BZprodA cz az tz) => h1.
rewrite (BZprod_eq2l bz (ZSp az tz) cz cnz h1) BZprodC.
apply:(BZdvds_pr1 tz az). 
Qed.

Lemma BZdvd_and_sum a a' b: b %|z a -> b %|z a' ->
  ( b %|z (a +z a') /\ (a +z a') %/z b =  (a %/z b) +z (a' %/z b)).
Proof. 
move => pa pb; move: (BZdvds_pr pa) (BZdvds_pr pb).
set q1 := a %/z b; set q2:= a' %/z b => e1 e2.
move: pa pb => [az bz _] [a'z _ _].
move: (ZS_quo az bz)(ZS_quo a'z bz) => q1z q2z.
have -> : a +z a' = b *z (q1 +z q2).
  by rewrite e1 e2  (BZprodDr bz q1z q2z).
case: (equal_or_not b \0z) => bnz.
   rewrite /q1 /q2 bnz !BZ_quo0 (BZsum_0r ZS0) BZprod_0r.
   split => //; apply: BZdvds_trivial.
rewrite (BZdvds_pr5 bz (ZSs q1z q2z) bnz);split => //.
rewrite BZprodC;apply: (BZdvds_pr1 (ZSs q1z q2z) bz).
Qed.

Lemma BZdvd_and_diff a a' b: b %|z a -> b %|z a'
  -> ( b %|z (a -z a') /\ (a -z a') %/z b =  (a %/z b) -z (a' %/z b)).
Proof. 
move => h1 h2; rewrite /BZdiff.
move:(h2) => [a'z _ _ ].
rewrite - (BZquo_opp2 h2).
move /(BZdvds_opp2 _ a'z): h2 => h3.
exact (BZdvd_and_sum h1 h3).
Qed.


(** ** Ideals *)

Definition BZ_ideal x:= 
  [/\ (forall a, inc a x -> intp a),
      (forall a b, inc a x -> inc b x -> inc (a +z b) x) &
      (forall a b, inc a x -> intp b -> inc (a *z  b) x)].

Definition BZ_ideal2 a b := Zo BZ (fun z =>
  exists u v, [/\ intp u, intp v & z = (a *z u) +z (b *z v)]).

Lemma BZ_in_ideal1 a b: intp a -> intp b ->
  (inc a (BZ_ideal2 a b) /\ inc b (BZ_ideal2 a b)).
Proof.
move: ZS1 ZS0 => z1 z0.
move => az bz; split; apply /Zo_P;split => //.
  by exists \1z,\0z; rewrite BZprod_0r BZprod_1r // BZsum_0r.
by exists \0z, \1z; rewrite BZprod_0r BZprod_1r // BZsum_0l.
Qed.

Lemma BZ_is_ideal2 a b: intp a -> intp b -> BZ_ideal (BZ_ideal2 a b).
Proof.
move => az bz.
split; first by move => x /Zo_P [].
  move => x y /Zo_P [xz [u [v [uz vz pa]]]] /Zo_P [yz [w [z [wz zz pb]]]].
  move: (ZSs uz wz) (ZSs vz zz) => ha hb.
  apply /Zo_P; split; first by apply:ZSs.
  exists (u +z w), (v +z z); split => //.
  rewrite (BZprodDr az uz wz) (BZprodDr bz vz zz).
  rewrite  BZsum_ACA; first (by  rewrite -pa -pb);by apply: ZSp.
move => x y /Zo_P [xz [u [v [uz vz pa]]]] yz.
apply /Zo_P; split; first by apply:ZSp.
exists (u *z y), (v *z y); split; try apply: ZSp => //.
rewrite (BZprodA az uz yz) (BZprodA bz vz yz).
by rewrite - (BZprodDl yz (ZSp az uz) (ZSp bz vz)) -pa.
Qed.

Definition BZ_ideal1 a := fun_image BZ (fun z => a *z z).

Lemma BZ_in_ideal3 a: intp a ->  BZ_ideal1 a = BZ_ideal2 a a.
Proof.
move: ZS0 => z0 az; set_extens t.
  move /funI_P => [x xz ->]; apply /Zo_P; split; first by apply: ZSp.
  by exists x, \0z;split => //; rewrite BZprod_0r BZsum_0r//; apply:ZSp.
move=> /Zo_P [xz [u [v [uz vz pa]]]]; apply /funI_P.
by exists (u +z v); [ apply:ZSs | rewrite (BZprodDr az uz vz) pa].
Qed.

Lemma BZ_in_ideal4 a: intp a -> 
   (BZ_ideal (BZ_ideal1 a) /\ inc a (BZ_ideal1 a)).
Proof. 
move=> az; rewrite (BZ_in_ideal3 az); split; first by apply: BZ_is_ideal2.
apply: (proj1 (BZ_in_ideal1 az az)).
Qed.

Lemma BZ_idealS_opp a x: BZ_ideal x -> inc a x -> inc (BZopp a) x.
Proof. 
move => [pa _ pb] ax; rewrite - (BZprod_m1r (pa _ ax)).
exact: (pb _ _ ax ZSm1).
Qed.

Lemma BZ_idealS_abs a x: BZ_ideal x -> inc a x -> inc (BZabs a) x.
Proof. 
move => pa pb.
case /BZ_i0P: (proj31 pa _ pb) => az; last by rewrite (BZabs_pos az).
by rewrite (BZabs_neg az); apply: BZ_idealS_opp.
Qed.

Lemma BZ_idealS_diff a b x:
 BZ_ideal x -> inc a x ->  inc b x ->  inc (a -z b) x.
Proof. 
move => ix ax bx; rewrite /BZdiff. 
apply (proj32 ix _ _ ax (BZ_idealS_opp ix bx)).
Qed.
 
Lemma BZ_idealS_rem a b x: BZ_ideal x -> inc a x ->  inc b x -> inc (a %%z b) x.
Proof. 
move => ix ax bx; rewrite /BZrem; apply: (BZ_idealS_diff ix ax).
exact: (proj33 ix _ _ bx (ZS_quo (proj31 ix _ ax) (proj31 ix _ bx))).
Qed.

Lemma BZ_ideal_0P a: inc a (BZ_ideal1 \0z) <->  (a = \0z).
Proof. 
split; first by move => /funI_P [z]; rewrite BZprod_0l.
by move => ->; apply /funI_P; exists \0z; [ apply: ZS0 |rewrite BZprod_0r].
Qed.

Lemma BZ_N_worder X: sub X BZp -> nonempty X ->
  exists2 a, inc a X & forall b, inc b X -> BZ_le a b.
Proof. 
move => pa [t tx];set (Y:= fun_image X P). 
have yb: sub Y Nat.
  move => y /funI_P [z zz ->]; apply: (BZ_valN (BZp_sBZ (pa _ zz))).
have ney: (nonempty Y) by exists (P t); apply /funI_P; ex_tac.
move: (Nat_order_wor) => [[or wor] sr].
have yb1: sub Y (substrate Nat_order) by rewrite sr.
move: (wor _ yb1 ney) => [y []]; rewrite iorder_sr // => yy aux.
move /funI_P: (yy) => [z zx pz]; ex_tac.
move => b bx;  apply /(zle_P1 (pa _ zx) (pa _ bx)); rewrite - pz.
have pby: inc (P b) Y by  apply /funI_P; ex_tac.
by move: (iorder_gle1 (aux _ pby)) => /Nat_order_leP [_ _].
Qed.


Theorem BZ_principal x: BZ_ideal x -> nonempty x ->
  exists2 a, inc a BZp & BZ_ideal1 a = x.
Proof. 
move => ix nex.
case: (p_or_not_p (exists2 a, inc a x & a <> \0z)); last first.
  move => h; exists \0z; first by apply: ZpS0.
  set_extens t.
    move:nex => [q qx]; move: (proj33 ix _ _ qx ZS0); rewrite BZprod_0r => tx.
    by move /BZ_ideal_0P => ->.
  move => tx; apply  /BZ_ideal_0P; ex_middle xnz; case: h;ex_tac.
move=> [a ax anz].
set (Z:= BZps \cap x).
have pa: sub Z BZp  by move => t /setI2_P [ta _]; apply: BZps_sBZp.
have pb: nonempty Z. 
   exists (BZabs a); apply/setI2_P; split; last by apply:BZ_idealS_abs.
   apply /zlt0xP; exact: (BZabs_positive  (proj31 ix _ ax) anz). 
move: (BZ_N_worder pa pb) => [b bz bm].
move /setI2_P: bz => [] /BZps_iP [bzp bnz] bx; ex_tac.
move: (BZp_sBZ bzp) => bz.
set_extens t.
  move/funI_P => [u uz ->]; apply: (proj33 ix _ _ bx uz).
move => tx.
move: (BZ_idealS_rem ix tx bx) => rx.
move: (BZdvd_correct (proj31 ix _ tx) bz bnz).
move => [qa qb [qc qd qe]].
case: (equal_or_not (t %%z b) \0z) => tnz.
  move: (ZSp bz qa) => pz. 
  rewrite qc tnz (BZsum_0r pz); apply /funI_P; exists (t %/z b) => //.
have rz: inc (t %%z b) Z by apply /setI2_P; split => //; apply  /BZps_iP.
move:qd (bm _ rz);rewrite (BZabs_pos bzp) => la lb; BZo_tac.
Qed.

Lemma BZ_ideal_unique_gen a b: intp a -> intp b ->
  BZ_ideal1 a = BZ_ideal1 b -> BZabs a = BZabs b.
Proof. 
move => az bz sv.
move: (BZ_in_ideal4 az) (BZ_in_ideal4 bz) => [pa pb] [_].
rewrite - sv => /funI_P [z zz eq1].
move: pb; rewrite sv  => /funI_P [u uz]; rewrite eq1.
rewrite - (BZprodA az zz uz) => aux.
move: (BZprod_abs az zz); rewrite - eq1;move => ->. 
move: (ZSa az) => aaz.
by case: (BZprod_1_inversion_more az zz uz aux); 
   move => ->; rewrite? BZabs_1 ? BZabs_0  ?BZabs_m1 ?BZprod_0l // BZprod_1r.
Qed.

Lemma BZ_ideal_unique_gen1 a b: inc a BZp -> inc b BZp ->
  BZ_ideal1 a = BZ_ideal1 b -> a = b.
Proof.
move => pa pb pc; move:(BZ_ideal_unique_gen (BZp_sBZ pa) (BZp_sBZ pb) pc).
by rewrite (BZabs_pos pa) (BZabs_pos pb).
Qed.

(** ** Gcd *)

Definition BZgcd a b := select (fun z => BZ_ideal1 z = BZ_ideal2 a b) BZp.
Definition BZlcm a b := (a *z b) %/z (BZgcd a b).

Lemma BZgcd_prop1 a b: intp a -> intp b ->
  (inc (BZgcd a b) BZp /\ BZ_ideal1  (BZgcd a b)  = BZ_ideal2 a b).
Proof. 
move => az bz.
set p :=  (fun z => BZ_ideal1 z = BZ_ideal2 a b).
have pa:  singl_val2 (inc^~ BZp) p.
  rewrite /p;move => x y /= pa e1 pb e2;apply: (BZ_ideal_unique_gen1 pa pb); ue.
move:(BZ_is_ideal2  az bz)=> idax.
have neid: nonempty (BZ_ideal2 a b).
   move: (proj1 (BZ_in_ideal1 az bz)) => pb; ex_tac.
move: (BZ_principal idax neid) => [c ca cb].
move: (select_uniq pa ca cb); rewrite /p -/(BZgcd a b) => <-;split => //.
Qed.

Lemma ZpS_gcd a b: intp a -> intp b -> inc (BZgcd a b) BZp.
Proof. move => az bz; exact: (proj1(BZgcd_prop1 az bz)). Qed.

Lemma ZS_gcd a b: intp a -> intp b -> intp (BZgcd a b).
Proof. move => az bz; exact: (BZp_sBZ (ZpS_gcd az bz)). Qed.

Lemma BZ_gcd_unq a b g: intp a -> intp b ->
  inc g BZp -> BZ_ideal1 g = BZ_ideal2 a b ->
   g = (BZgcd a b).
Proof.
move => az bz gp idp.
set p :=  (fun z => BZ_ideal1 z = BZ_ideal2 a b).
have un: (forall x y, inc x BZp -> inc y BZp -> p x -> p y -> x = y).
  rewrite /p;move => x y pa pb e1 e2; apply: (BZ_ideal_unique_gen1 pa pb); ue.
move:(BZgcd_prop1 az bz) => [pa pb].
exact (un _ _ gp pa idp pb).
Qed.

Lemma BZgcd_x1 x: intp x -> BZgcd x \1z = \1z.
Proof.
move: ZS0 ZS1=> z0 z1 h; symmetry. apply: (BZ_gcd_unq h ZS1 (BZps_sBZp ZpsS1)).
set_extens t.
  move /funI_P => [z zz ->]; apply/Zo_P; split; first by rewrite (BZprod_1l zz).
  by exists \0z, z; split => //; rewrite BZprod_0r BZprod_1l // BZsum_0l.
move => /Zo_P [tZ [u [v [uz vz ->]]]].
set w := (x *z u +z \1z *z v).
have wz: inc w BZ by apply:ZSs; apply: ZSp.
by apply/funI_P; ex_tac; rewrite BZprod_1l.
Qed.

Lemma BZgcd_div a b (g:= (BZgcd a b)): intp a -> intp b ->
  a = g *z  (a %/z g) /\ b = g *z  (b %/z g).
Proof.
move => az bz; move: (BZgcd_prop1 az bz)=> [pa pb];move: (BZp_sBZ pa) => pc.
move: (BZ_in_ideal1 az bz); rewrite - pb -/g. 
move => [] /funI_P [q qa qb] /funI_P [q' qa' qb'].
split.
apply: BZdvds_pr; rewrite qb; rewrite BZprodC;apply: (BZdvds_pr1 qa pc).
apply: BZdvds_pr; rewrite qb'; rewrite BZprodC;apply: (BZdvds_pr1 qa' pc).
Qed.

Lemma BZgcd_nz a b: intp a ->  intp b -> 
  BZgcd a b = \0z ->  (a = \0z /\ b = \0z).
Proof. 
by move => az bz h; move: (BZgcd_div az bz); rewrite h !BZprod_0l.
Qed.

Lemma BZgcd_nz1 a b: intp a ->  intp b -> 
  (a <> \0z \/ b <> \0z) -> BZgcd a b <> \0z.
Proof. 
by move => az bz h gnz; move: (BZgcd_nz az bz gnz) => [a0 b0]; case: h.
Qed.

Lemma BZ_nz_quo_gcd a b: intp a -> intp b -> a <> \0z -> 
   a %/z (BZgcd a b) <> \0z.
Proof. 
by move => az bz anz qz; move: (proj1 (BZgcd_div az bz)); rewrite qz BZprod_0r.
Qed.

Lemma BZ_positive_quo_gcd a b: inc a BZp -> intp b -> 
  inc (a %/z (BZgcd a b)) BZp.
Proof. 
move => azp bz; apply:ZpS_quo => //; apply: (ZpS_gcd (BZp_sBZ azp) bz).
Qed.

Lemma BZgcd_prop2 a b: intp a -> intp b ->
  (exists x y, [/\ intp x, intp y  &
    (BZgcd a b =  (a *z x) +z (b *z y))]).
Proof. 
move => az bz; move: (BZgcd_prop1 az bz) => [pa pb].
by move: (BZ_in_ideal4 (BZp_sBZ pa)) => [_]; rewrite pb => /Zo_P [_].
Qed.

Lemma BZgcd_C a b: BZgcd a b = BZgcd b a.
Proof. 
suff: BZ_ideal2 a b =  BZ_ideal2 b a by  rewrite /BZgcd => ->.
by set_extens t => /Zo_P [pa [u [v [uc vz etc]]]]; apply:Zo_i => //;
  exists v ;exists u; rewrite BZsumC.
Qed.

Lemma BZgcd_opp a b: intp a -> intp b -> BZgcd a b = BZgcd (BZopp a) b.
Proof. 
move => az bz.
suff: BZ_ideal2 a b =  BZ_ideal2 (BZopp a) b by  rewrite /BZgcd => ->.
set_extens t => /Zo_P [pa [u [v [uc vz etc]]]]; apply:Zo_i => //;
  exists (BZopp u), v;split => //; try apply:ZSo => //.
  by rewrite BZprod_opp_opp.
by rewrite BZprod_opp_comm.
Qed.

Lemma BZ_gcd_abs1 a b: intp a -> intp b -> BZgcd (BZabs a) b = BZgcd a b.
Proof.
move => uz vz; case /BZ_i0P: (uz) => su.
  by rewrite (BZabs_neg su) (BZgcd_opp uz vz). 
by rewrite (BZabs_pos su).
Qed.

Lemma BZ_gcd_abs2 a b: intp a -> intp b ->  BZgcd a (BZabs b) = BZgcd a b.
Proof.
by move => az bz; rewrite (BZgcd_C a) (BZgcd_C a) BZ_gcd_abs1.
Qed.

Lemma BZ_gcd_abs a b: intp a -> intp b ->
   BZgcd (BZabs a) (BZabs b) = BZgcd a b.
Proof.
move => az bz. 
by rewrite (BZ_gcd_abs1 az (ZSa bz)) (BZ_gcd_abs2 az bz).
Qed.

Lemma BZgcd_s2 a b (g:= (BZgcd a b)): intp a -> intp b ->
  [/\ inc g BZ, inc (a %/z g) BZ & inc (b %/z g) BZ].
Proof.
by move => az bz; move: (ZS_gcd az bz) => pz; split => //; apply: ZS_quo.
Qed.

Lemma BZgcd_id a: intp a -> BZgcd a a = BZabs a.
Proof.
move => az; rewrite - (BZ_gcd_abs az az); set b := BZabs a.
move: (BZabs_iN  az) => bzp; move: (BZp_sBZ bzp) => bz.
by rewrite - (BZ_gcd_unq bz bz bzp (BZ_in_ideal3 bz)).
Qed.

Lemma BZgcd_rem a b q: intp a -> intp b -> intp q ->
    BZgcd a (b +z a *z q)  = BZgcd a b.
Proof.
move => az bz qz.
suff: BZ_ideal2 a b =  BZ_ideal2 a (b +z a *z q) by rewrite /BZgcd => ->.
move: (ZSp az qz) => aqz.
set_extens t => /Zo_P [pa [u [v [uz vz etc]]]]; apply:Zo_i => //.
   move:(ZSp vz qz) => vqz; move: (ZS_diff uz vqz)=> ha. 
   exists (u -z v *z q); exists v;split => //.
   move: (ZSp aqz vz)=> pa1.
   rewrite (BZprodBr az uz vqz) (BZprodDl vz bz aqz).
   rewrite (BZprodC v) (BZprodA az qz vz).
   rewrite (BZsum_ACA (ZSp az uz)(ZSo pa1) (ZSp bz vz) pa1) - etc.
   by rewrite (BZsumC _ ((a *z q) *z v)) - /(_ -z _) (BZdiff_diag pa1) BZsum_0r.
move : etc; rewrite (BZprodDl vz bz aqz) (BZsumC (b  *z v)).
rewrite (BZsumA (ZSp az uz) (ZSp aqz vz) (ZSp bz vz)) - (BZprodA az qz vz).
move: (ZSp qz vz) => qvz.
rewrite -(BZprodDr az uz qvz) => ->.
by exists (u +z q *z v); exists v; split => //; apply: ZSs.
Qed.


Lemma BZgcd_sum a b: intp a -> intp b ->  BZgcd a (b +z a)  = BZgcd a b.
Proof.
move => az bz; move: (BZgcd_rem az bz ZS1).
by rewrite (BZprod_1r az).
Qed.

Lemma BZgcd_diff a b: intp a -> intp b ->  BZgcd a (b -z a)  = BZgcd a b.
Proof.
move => az bz; move: (BZgcd_rem az bz ZSm1).
by rewrite (BZprod_m1r az).
Qed.

Lemma BZgcd_zero a: intp a -> BZgcd a \0z = BZabs a.
Proof. 
by move => az; move:(BZgcd_diff az az); rewrite (BZdiff_diag az) (BZgcd_id az).
Qed.

Lemma ZS_lcm a b: intp a -> intp b -> intp (BZlcm a b).
Proof. 
move => az bz; move: (ZS_gcd az bz) => gz.
apply: (ZS_quo (ZSp az bz) gz).
Qed.

Lemma BZlcm_zero a: intp a -> BZlcm a \0z = \0z.
Proof. 
move => az; rewrite /BZlcm BZprod_0r.
exact (proj2 (BZ_quorem00 (BZp_sBZ (ZpS_gcd az ZS0)))).
Qed.

Lemma BZlcm_C a b: BZlcm a b = BZlcm b a.
Proof.  by rewrite /BZlcm BZprodC BZgcd_C. Qed.


Lemma BZlcm_prop1 a b (g := BZgcd a b) (l := BZlcm a b): 
  intp a -> intp b -> 
  [/\ l =  (a %/z g) *z b, l = a *z (b %/z g) &
    l =  ((a %/z g) *z (b %/z g)) *z g].
Proof. 
move => az bz.
move: (ZS_gcd az bz) => gz. 
case:(equal_or_not b \0z) => bnz.
   rewrite /l bnz (BZlcm_zero az) BZprod_0r.
   by rewrite (proj2 (BZ_quorem00 gz)) !BZprod_0r BZprod_0l.
move: (BZgcd_div az bz); rewrite -/g.
set q1:= (a %/z g); set q2 := (b %/z g);  move => [pa pb].
move: (ZS_quo az gz) (ZS_quo bz gz) => q1z q2z.
suff:  l = q1 *z b.
  move => ->;split => //; rewrite  pb  ? pa.
   by rewrite (BZprodA q1z gz q2z) (BZprodC g _).
   by rewrite (BZprodC g _) (BZprodA q1z q2z gz).
rewrite/l/BZlcm{1} pa -(BZprodA gz q1z bz); apply:(BZdvds_pr5 gz (ZSp q1z bz)).
by apply: (BZgcd_nz1 az bz); right.
Qed.

Lemma BZlcm_nz a b: intp a -> intp b ->
  a <> \0z -> b <> \0z -> BZlcm a b <> \0z.
Proof.
move=> az bz ane bnz.
move: (BZp_sBZ(ZpS_gcd az bz)) => gz.
move: (BZlcm_prop1 az bz).
set u := (a %/z BZgcd a b); move => [h _ _]; rewrite h.
apply:(BZprod_nz (ZS_quo az gz) bz _ bnz) => h1.
by move: (proj1(BZgcd_div az bz)); rewrite h1 BZprod_0r.
Qed.

Lemma BZgcd_div2 a b: intp a -> intp b -> BZgcd a b %|z a.
Proof.
move => aZ bZ.
move:(BZgcd_div aZ bZ) => [ ha _]; rewrite {2} ha.
move:  (ZS_gcd aZ bZ) => hb; move: (ZS_quo  aZ hb) => hc.
apply: (BZdvds_pr1' hc (ZS_gcd aZ bZ)).
Qed.


Definition BZcoprime a b :=  BZgcd a b = \1z.
Definition Bezout_rel a b u v :=  (a *z u) +z (b *z v) = \1z.
Definition BZBezout a b :=
  exists u v, [/\ intp u, intp v & Bezout_rel a b u v].

Lemma BZcoprime_sym a b: BZcoprime a b -> BZcoprime b a.
Proof. by rewrite /BZcoprime BZgcd_C. Qed.

Lemma BZcoprime_add a b: intp a -> intp b ->
  BZcoprime a b -> BZcoprime a (a +z b).
Proof. 
move => az bz; rewrite /BZcoprime.
by rewrite -(BZgcd_rem az bz ZS1) (BZprod_1r az) BZsumC.
Qed.

Lemma BZcoprime_diff a b: intp a -> intp b ->
  BZcoprime a b -> BZcoprime a (b -z a).
Proof. 
move => az bz; rewrite /BZcoprime /BZdiff -(BZprod_m1r az).
by rewrite -(BZgcd_rem az bz ZSm1). 
Qed.

Lemma BZ_Bezout_if_coprime a b: intp a -> intp b ->
  BZcoprime a b -> BZBezout a b.
Proof. 
move => az bz; move:(BZgcd_prop2 az bz) => [x [y [xz yz ha]]] hb.
by exists x,y; split => //; rewrite /Bezout_rel - ha.
Qed.

Lemma BZ_coprime_if_Bezout a b: intp a -> intp b ->
  BZBezout a b -> BZcoprime a b.
Proof. 
move => az bz [x [y [xz yz etc]]]; red; symmetry.
apply:(BZ_gcd_unq az bz (BZps_sBZp ZpsS1)).
set_extens t.
  move => /funI_P [z zz]; rewrite  (BZprod_1l zz) => ->.
  move: (ZSp xz zz)(ZSp yz zz) => pa pb.
  apply /Zo_P;split => //; exists (x *z z);exists (y *z z);split => //.
  rewrite (BZprodA az xz zz) (BZprodA bz yz zz).
 by rewrite - (BZprodDl zz (ZSp az xz)(ZSp bz yz)) etc BZprod_1l.
move => /Zo_P [tz _]; apply /funI_P; ex_tac; symmetry;exact (BZprod_1l tz).
Qed.


Lemma BZ_Bezout_cofactors a b: intp a -> intp b ->
  (a<> \0z \/ b <> \0z) ->
  BZBezout (a %/z (BZgcd a b)) (b %/z (BZgcd a b)).
Proof. 
move => az bz h.
move:(BZgcd_prop2 az bz); set g := (BZgcd a b); move => [x [y [xz yz]]].
move: (BZgcd_div az bz) => []; rewrite -/g => p1 p2.
rewrite {1} p1 {1} p2; set qa := (a %/z g); set qb:= (b %/z g).
move: (BZp_sBZ (ZpS_gcd az bz)) => gz.
move: (ZS_quo az gz) (ZS_quo bz gz) => pa pb.
rewrite - (BZprodA gz pa xz) - (BZprodA gz pb yz).
rewrite - (BZprodDr gz (ZSp pa xz) (ZSp pb yz)).
rewrite/g  - {1} (BZprod_1r gz) => h1.
exists x; exists y;split => //; symmetry.
by apply: (BZprod_eq2l ZS1 _ gz (BZgcd_nz1 az bz h) h1); apply:ZSs; apply:ZSp.
Qed.

Lemma BZ_coprime1r  a: intp a -> BZcoprime a \1z.
Proof. 
move: ZS1 ZS0=> oz zz az;apply (BZ_coprime_if_Bezout az oz).
by exists \0z, \1z;  rewrite /Bezout_rel BZprod_0r BZprod_1r // BZsum_0l.
Qed.

Lemma BZ_coprime1l a: intp a -> BZcoprime \1z a.
Proof. by move => az; apply:BZcoprime_sym; apply:BZ_coprime1r. Qed.

Definition BZdvdorder := graph_on BZdivides BZps.

Lemma BZdvds_pr6 a b: intp a -> intp b ->
  (a %|z b <-> sub (BZ_ideal1 b)(BZ_ideal1 a)).
Proof. 
move => az bz; split.
  move => d1 x /funI_P [y yz ->].
  rewrite (BZdvds_pr d1) -( BZprodA az (ZS_quo bz az) yz); apply /funI_P.
  by exists ((b %/z a) *z y) => //; apply: ZSp=> //; apply: ZS_quo.
move=> h; move: (h _ (proj2 (BZ_in_ideal4 bz))) => /funI_P [z zz ->].
rewrite BZprodC; apply: (BZdvds_pr1 zz az).
Qed.

Lemma BZdvds_pr6' a b: a %|z b -> sub (BZ_ideal1 b)(BZ_ideal1 a).
Proof.
move => h; move: (h) => [pa pb pc].
by apply/(BZdvds_pr6 pb pa).
Qed.

Lemma BZdvds_monotone a b: inc b BZps -> a %|z b -> a <=z b.
Proof. 
move => /BZps_iP [bzp bnz] dvd; move: (dvd) => [_ az  _].
case /BZ_i0P: az => ap.
  move:(BZms_sBZ ap)(BZp_sBZ bzp) => az bz.
  split => //; constructor 2. 
  by rewrite /int_np /int_pp (BZp_sg bzp) (BZms_sg ap).
move: (BZdvds_pr dvd) => eq.
rewrite eq; apply: (BZprod_Mpp ap).
apply /BZps_iP;split => //; first by apply : (ZpS_quo bzp ap).
by dneg h; rewrite eq h BZprod_0r.
Qed.

Lemma BZdvdorder_or: order BZdvdorder.
Proof.
have aux: forall t, inc t BZps -> [/\ inc t BZ, inc t BZp & t <> \0z].
   move => t /BZps_iP [h unz]; split => //; exact (BZp_sBZ h).
apply: order_from_rel1.
    move => y x z pa pb; apply: (BZdvds_trans pb pa).
  move => u v pa pb d1 d2.
  move: (BZdvds_monotone pa d2)(BZdvds_monotone pb d1) => l1 l2; BZo_tac.
move => u h; move: (aux _ h) => [uz _ unz].
exact (proj1 (BZdvd_itself uz unz)).
Qed.

Definition BZgcd_prop a b p :=
   [/\ p %|z a, p %|z b  & forall t, t %|z a  -> t %|z b  -> t %|z p].

Definition BZgcdp_prop a b p :=
   [/\ inc p BZp, p %|z a, p %|z b  & 
    forall t, inc t BZp ->  t %|z a  -> t %|z b  -> t %|z p].

Lemma BZgcd_prop3 a b: intp a -> intp b ->
   (BZgcd_prop a b (BZgcd a b) 
       /\ forall g,  BZgcd_prop a b g -> (BZgcd a b) = BZabs g).
Proof.
move => az bz.
move: (ZS_gcd az bz) => gz.
move: (BZgcd_div az bz) (ZS_quo az gz)(ZS_quo bz gz) => [pa pb] sa sb.
set G := BZgcd a b.
have r1:G %|z a by rewrite pa BZprodC;apply:(BZdvds_pr1 sa gz).
have r2:G %|z b by rewrite pb BZprodC;apply:(BZdvds_pr1 sb gz).
have r3:forall u : Set, u %|z a -> u %|z b -> u %|z G.
  move => u ua ub; move: (ua) => [_ uz _].
  move:  (ZS_quo az uz) (ZS_quo bz uz) => paz pbz.
  rewrite /G;move: (BZgcd_prop2 az bz) => [x [y [xz yz ->]]].
  move:  (ZSp paz xz)  (ZSp pbz yz) => qaz qbz.
  rewrite (BZdvds_pr ua) (BZdvds_pr ub) - (BZprodA uz  paz xz). 
  rewrite - (BZprodA uz pbz yz)- (BZprodDr uz qaz qbz) BZprodC.
  apply: (BZdvds_pr1 (ZSs qaz qbz) uz). 
split;first by split.
move => g [gp1 gp2 gp3].
move: (extensionality (BZdvds_pr6' (gp3 _ r1 r2))(BZdvds_pr6'  (r3 _ gp1 gp2))).
move: (gp1)(r1) => [_ gZ _]  [_ GZ _].
move=> et; rewrite (BZ_ideal_unique_gen gZ GZ et).
by rewrite /G (BZabs_pos (ZpS_gcd az bz)).
Qed.

Lemma BZgcd_prop3' a b: intp a -> intp b ->  
   (BZgcdp_prop a b (BZgcd a b) 
       /\ forall g,  BZgcdp_prop a b g -> (BZgcd a b) = g).
Proof.
move => az bz.
move:(ZpS_gcd az bz) => hb.
move: (BZgcd_prop3 az bz) => [[pa pb pc] pd].
have pr t: inc t BZp -> t %|z a -> t %|z b -> t %|z BZgcd a b.
  by move => ta tb tc; apply: pc.
split; first done.
move => g [gp ga gb gc].
suff: BZgcd_prop a b g by move/pd; rewrite BZabs_pos.
suff : forall t, t %|z a -> t %|z b -> t %|z g by split.
move => t ta tb.
move: (ta) => [_ tu _].
case /BZ_i1P: (tu) => tp.
+ by move: ta tb; rewrite tp; apply: gc; apply:ZpS0.
+ by apply: gc => //; apply:BZps_sBZp.
+ move:(BZopp_negative1 tp) => otp.
  move/(BZdvds_opp1 _ tu): ta => ta1.
  move/(BZdvds_opp1 _ tu): tb => tb1. 
  apply/(BZdvds_opp1 _ tu); exact: (gc _ (BZps_sBZp otp) ta1 tb1).
Qed.

Lemma BZlcm_prop2 a b (l := BZlcm a b): 
  intp a -> intp b -> 
  [/\ a %|z l, b %|z  l & forall u, a %|z  u ->  b  %|z u ->  l  %|z  u].
Proof.
move => az bz ; rewrite /l.
move: (BZlcm_prop1 az bz) => [pa pb pc].
move: (ZS_gcd az bz) => gz.
split; first by rewrite pb BZprodC;  apply: (BZdvds_pr1 (ZS_quo bz gz) az).
   by rewrite pa; apply: (BZdvds_pr1 (ZS_quo az gz) bz).
move => u ua ub.
case: (equal_or_not a \0z) => anz.
   move: ua; rewrite anz; move /BZdvds_trivial_rec => ->.
   rewrite BZlcm_C (BZlcm_zero bz); exact (proj1(BZdvd_zero1 ZS0)).
have h: a <> \0z \/ b <> \0z by left.
move: (BZdvds_pr ua) (BZdvds_pr ub) => r1 r2.
move:  (BZ_Bezout_cofactors az bz h) => [x [y [xz yz eq1]]].
move: (f_equal (fun z => z *z u) eq1).
move:(ua) => [uz _ _].
move: (ZS_quo az gz) (ZS_quo bz gz).
set a' := (a %/z BZgcd a b); set b' := (b %/z BZgcd a b).
move => a'z b'z.
move:(ZS_quo uz bz)(ZS_quo uz az) (ZS_lcm az bz) => ubz uaz lz.
move: (ZSp xz ubz)(ZSp yz uaz) => aaz bbz.
rewrite (BZprod_1l uz) (BZprodDl uz (ZSp a'z xz) (ZSp b'z yz)) => <-.
set a1 := (a' *z x) *z u ; set a2 := (b' *z y) *z u.
have ->: a2 = y *z ((u %/z a) *z BZlcm a b).
  rewrite /a2 (BZprodC _ u) (BZprodA uz b'z yz).
  by rewrite {1} r1 (BZprodC a) -(BZprodA uaz az b'z) - pb BZprodC.
have ->: a1 = x *z ((u %/z b) *z BZlcm a b).
  rewrite /a1 (BZprodC _ u) (BZprodA uz a'z xz). 
  by rewrite {1} r2 (BZprodC b) -(BZprodA ubz bz a'z) (BZprodC b) pa  BZprodC.
rewrite (BZprodA yz uaz lz) (BZprodA xz ubz lz) - (BZprodDl lz aaz bbz).
apply: (BZdvds_pr1 (ZSs aaz bbz) lz). 
Qed.



Lemma BZ_lcm_prop3 a b u: BZcoprime a b -> 
  a  %|z u -> b  %|z u ->  (a *z b)  %|z u.
Proof. 
move => g1 au bu.
move: (au) (bu) => [uz az  _] [_ bz  _].
move: (proj33 (BZlcm_prop2 az bz) _ au bu).
by rewrite /BZlcm g1 (BZquo_one (ZSp az bz)).
Qed.

Lemma BZdvdorder_sr: substrate BZdvdorder = BZps.
Proof.
rewrite /BZdvdorder  graph_on_sr //.
by move => a /BZps_iP [ap anz]; move: (BZdvd_itself (BZp_sBZ ap) anz)=> [].
Qed.

Lemma BZdvdorder_gle x y: 
  gle BZdvdorder x y <-> [/\ inc x BZps, inc y BZps & x %|z y].
Proof. exact: graph_on_P1. Qed.


Lemma BZpsS_gcd x y: inc x BZps -> inc y BZps -> inc (BZgcd x y) BZps.
Proof.
move =>  xs ys.
move /BZps_iP: (xs) => [pa xnz]; move: (BZp_sBZ pa) => xz.
move /BZps_iP: (ys) => [pb ynz]; move: (BZp_sBZ pb) => yz.
have h: (x <> \0z \/ y <> \0z) by left.
apply /BZps_iP; split;[ by apply: ZpS_gcd | exact (BZgcd_nz1 xz yz h)].
Qed.

Lemma BZpsS_lcm x y: inc x BZps -> inc y BZps -> inc (BZlcm x y) BZps.
Proof.
move =>  xs ys.
move /BZps_iP: (xs) => [pa xnz]; move: (BZp_sBZ pa) => xz.
move /BZps_iP: (ys) => [pb ynz]; move: (BZp_sBZ pb) => yz.
apply /BZps_iP; split; last by apply: (BZlcm_nz xz yz xnz ynz).
rewrite /BZlcm; apply: ZpS_quo; last by apply: ZpS_gcd. 
by apply: ZpS_prod.
Qed.


Lemma BZdvd_lattice_aux x y: inc x BZps -> inc y BZps ->
  (least_upper_bound BZdvdorder (doubleton x y) (BZlcm x y)
   /\ (greatest_lower_bound BZdvdorder (doubleton x y) (BZgcd x y))).
Proof.
move:  BZdvdorder_or => or.
move: BZdvdorder_gle => H.
move =>  xs ys.
move: (BZpsS_gcd xs ys) (BZpsS_lcm xs ys) => gp lp.
move:(BZps_sBZ xs) (BZps_sBZ ys) => xz yz.
split.
  move: (BZlcm_prop2 xz yz) => [p1 p2 p3].
  apply: (lub_set2 or); try apply /H => //.
   move => t; move/H => [_ ts ta]/H [_ _ tb]; move: (p3 _ ta tb) => tc. 
   by apply/H.
move: (BZgcd_prop3 xz yz) => [[p1 p2 p3] _].
apply: (glb_set2 or); 
  last (move => t; move/H => [ts _ ta] /H [_ _ tb]; move: (p3 _ ta tb) => tc);
  by apply /H.
Qed.

Lemma BZdvd_lattice: lattice BZdvdorder.
Proof.
split; first by apply:  BZdvdorder_or.
move => x y; rewrite BZdvdorder_sr => xs ys.
move:  (BZdvd_lattice_aux xs ys) => [pa pb].
split; [ by exists  (BZlcm x y) | by exists  (BZgcd x y) ].
Qed.


Lemma BZdvd_sup x y: inc x BZps -> inc y BZps ->
  sup  BZdvdorder x y = BZlcm x y.
Proof.
move => xs ys; move:  (BZdvd_lattice_aux xs ys) => [pa pb].
symmetry; apply: (supremum_pr2 BZdvdorder_or pa).
Qed.

Lemma BZdvd_inf x y: inc x BZps -> inc y BZps ->
  inf BZdvdorder x y = BZgcd x y.
Proof.
move => xs ys; move:  (BZdvd_lattice_aux xs ys) => [pa pb].
symmetry; apply: (infimum_pr2 BZdvdorder_or pb).
Qed.


Lemma BZgcd_A a b c: intp a -> intp b -> intp c ->
   (BZgcd a (BZgcd b c)) = (BZgcd (BZgcd a b) c).
Proof.
move => az bz cz.
move: (lattice_props (BZdvd_lattice)); rewrite BZdvdorder_sr.
move =>[_ [_ [_ [_ [ _ [h _]]]]]].
have Ha t: intp t -> BZgcd   \0z t = BZabs t.
  by move => rp; rewrite BZgcd_C BZgcd_zero.
have Hb x y: intp x -> intp y -> BZabs (BZgcd x y) = BZgcd x y.
  move => xz yz; exact: (BZabs_pos (ZpS_gcd xz yz)).
rewrite - (BZ_gcd_abs az (ZS_gcd bz cz)) (Hb _ _ bz cz).
rewrite - (BZ_gcd_abs  (ZS_gcd az bz) cz) (Hb _ _ az bz).
rewrite - (BZ_gcd_abs az bz) - (BZ_gcd_abs bz cz).
move: (BZabs_iN az) (BZabs_iN bz)(BZabs_iN cz).
set x := BZabs a; set y := BZabs b; set z := BZabs c.
move=> xp yp zp.
move: (BZp_sBZ xp) (BZp_sBZ yp) (BZp_sBZ zp) => xz yz zz. 
case: (equal_or_not x \0z) => xnz.
  rewrite xnz (Ha y yz) (Ha _ (ZS_gcd yz zz)) (Hb _ _ yz zz).
  by rewrite (BZ_gcd_abs1 yz zz).
case: (equal_or_not y \0z) => ynz.
  by rewrite ynz (Ha z zz)  (BZgcd_zero xz) (BZabs_pos zp)  (BZabs_pos xp).
case: (equal_or_not z \0z) => znz.
  rewrite znz (BZgcd_zero yz) (BZgcd_zero (ZS_gcd xz yz)) (Hb _ _ xz yz).
  by rewrite (BZ_gcd_abs2 xz yz).
have xx:inc x BZps by  apply/BZps_iP.
have yy:inc y BZps by  apply/BZps_iP.
have zza:inc z BZps by  apply/BZps_iP.
move: (h _ _ _ xx yy zza).
rewrite (BZdvd_inf yy zza) (BZdvd_inf xx yy).
rewrite (BZdvd_inf xx (BZpsS_gcd yy zza)).
by rewrite (BZdvd_inf (BZpsS_gcd xx yy) zza).
Qed.

  
Lemma BZgcd_A_alt a b c: intp a -> intp b -> intp c ->
   (BZgcd a (BZgcd b c)) = (BZgcd (BZgcd a b) c).
Proof.
move => az bz cz.
pose id3 u v w := Zo BZ (fun t=> exists x y z,
    [/\ intp x, intp y, intp z &
    t = u *z x +z (v *z y +z w *z z)]).
have id3a: id3 a b c = id3 c a b.
  set_extens t => /Zo_P [tz [x [y [z [xz yz zz etc]]]]]; apply: Zo_i => //.
     exists z; exists x; exists y;split => //; rewrite etc (BZsumC (c *z z)).
     by apply:BZsumA; apply:ZSp.
  exists y; exists z; exists x; split => //;rewrite etc BZsumC.
     by symmetry;apply:BZsumA; apply: ZSp.
have aux: forall u v w, inc u BZ -> inc v BZ -> inc w BZ ->
   BZ_ideal1 (BZgcd u (BZgcd v w)) = id3 u v w.
  move => u v w uz vz wz.
  move:(BZgcd_prop2 vz wz)=> [uu [vv [uuz vvz etc]]].
  rewrite (proj2 (BZgcd_prop1 uz (ZS_gcd vz wz))). 
  set_extens t; move => /Zo_P [tz h]; apply: (Zo_i tz). 
    move: h => [c1 [c2 [c1z c2z ->]]]; rewrite etc.
    exists c1; exists (uu *z c2); exists (vv *z c2).
    rewrite  (BZprodDl c2z (ZSp vz uuz) (ZSp wz vvz)).
    rewrite - (BZprodA vz uuz c2z) - (BZprodA wz vvz c2z).
    move: (ZSp uuz c2z)(ZSp vvz c2z) => sa sb; split => //.
  move: h=> [x [y [z [xz yz zz]]]].
  move: (BZgcd_div vz wz).
  move: (ZS_gcd vz wz) => gz; move: (ZS_quo vz gz)(ZS_quo wz gz).
  set q1 := (v %/z BZgcd v w); set q2:=(w %/z BZgcd v w); set g := BZgcd v w.
  move => sa sb [-> ->].
  move:  (ZSp sa yz) (ZSp sb zz) => sc sd; move:(ZSs sc sd) => se.
  rewrite - (BZprodA gz sa yz) - (BZprodA gz sb zz).
  rewrite  - (BZprodDr gz sc sd).
  move => ->; exists x; exists ((q1 *z y +z q2 *z z)); split => //.
rewrite (BZgcd_C (BZgcd a b)).
have pa:=(ZpS_gcd az (ZS_gcd bz cz)).
have pb:= (ZpS_gcd cz (ZS_gcd az bz)). 
move: (aux _ _ _ az bz cz); rewrite id3a - (aux _ _ _ cz az bz).
move => h; exact: (BZ_ideal_unique_gen1 pa pb h).
Qed.

Lemma BZgcd_prodD a b c: intp a -> intp b -> inc c BZp ->
   (BZgcd (c *z a) (c *z b)) = c *z (BZgcd a b).
Proof.
move => az bz cp; move: (BZp_sBZ cp) => cz.
move: (BZgcd_prop3 (ZSp cz az)(ZSp cz bz)).
move => [_ sd].
move: (BZgcd_prop3 az bz) => [[sa sb sc] _].
set g := c *z BZgcd a b.
move: (ZpS_gcd az bz) => gzp; move: (BZp_sBZ gzp) => gz.
have ->: g = BZabs g.
   by rewrite /g (BZprod_abs cz gz) (BZabs_pos cp)(BZabs_pos gzp).
case: (equal_or_not c \0z) => cnz.
   by rewrite /g cnz !BZprod_0l (BZgcd_zero ZS0).
apply: sd;split.
    rewrite /g (BZprodC c) (BZprodC c).
    by move /(BZdvds_prod (ZS_gcd az bz) az cz cnz): sa.
  rewrite /g (BZprodC c) (BZprodC c).
  by move/(BZdvds_prod (ZS_gcd az bz) bz cz cnz): sb.
move => u u1 u2; move:  (BZdvds_pr u1) (BZdvds_pr u2).
move: u1 => [_ uz  _].
move: (ZS_quo (ZSp cz az) uz) (ZS_quo (ZSp cz bz) uz).
set c1:= ((c *z a) %/z u) ; set c2 := ((c *z b) %/z u) => c1z c2z.
move: (BZgcd_prop2 az bz) => [x [y [xz yz etc]]] e1 e2.
rewrite /g etc (BZprodDr cz (ZSp az xz)(ZSp bz yz)).
rewrite (BZprodA cz az xz)(BZprodA cz bz yz) e1 e2.
rewrite -{1} (BZprodA uz c1z xz) - (BZprodA uz c2z yz). 
move: (ZSp c1z xz)(ZSp c2z yz) => qa qb;  move: (ZSs qa qb) => qc.
rewrite -(BZprodDr uz qa qb); apply (BZdvds_pr1'  qc uz).
Qed.

Lemma BZgcd_simp a b c: intp a -> intp b -> intp c ->
   BZcoprime a b -> BZgcd a (b *z c) = BZgcd a c.
Proof.
move => az bz cz cop.
move: (BZ_Bezout_if_coprime az bz cop) => [x [y [xz yz etc]]].
move: (f_equal (fun z => z *z c) etc).
rewrite (BZprod_1l cz)  (BZprodDl cz (ZSp az xz)(ZSp bz yz)).
rewrite - (BZprodA az xz cz) (BZprodC b) - (BZprodA yz bz cz).
move: (ZSp xz cz); set u := (x *z c) => uz eq1.
move: (BZgcd_prop3 az (ZSp bz cz) ) => [_ h].
move: (BZgcd_prop3 az cz) => [[pa pb pc] _].
rewrite - (BZabs_pos (ZpS_gcd az cz)); apply: h.
split; first by exact.
   by apply: (BZdvds_trans2 bz pb).
move=> t ta tb; apply: pc; [ exact | rewrite - eq1 ].
have p1:  t %|z (a *z u) by exact (BZdvds_trans (BZdvds_pr1' uz az) ta).
move: (ZSp az uz) => auz.
have p2: t %|z  (y *z (b *z c)).
  rewrite BZprodC; exact: (BZdvds_trans (BZdvds_pr1' yz (ZSp bz cz)) tb).
exact (proj1 (BZdvd_and_sum p1 p2)).
Qed.

Lemma  BZdvd_latticeD: distributive_lattice1 BZdvdorder.
Proof.
suff: forall a b g z, inc a BZps -> inc b BZps -> inc g BZps -> inc z BZps -> 
 BZBezout a b -> BZgcd z ((a *z b) *z g) %|z BZlcm (g *z a) (BZgcd (g *z b) z).
move => h.
  apply:(proj32 (distributive_lattice_prop2 BZdvd_lattice)).
  apply /(distributive_lattice_prop3  BZdvd_lattice).
  move => x y z; rewrite BZdvdorder_sr => xs ys zs.
  rewrite (BZdvd_inf ys zs) (BZdvd_sup xs ys).
  move: (BZpsS_gcd ys zs)  (BZpsS_lcm xs ys)  (BZpsS_gcd xs ys)=> gs ls g1s.
  rewrite (BZdvd_inf zs ls) (BZdvd_sup xs gs).
  apply /BZdvdorder_gle; split; first by apply:  (BZpsS_gcd zs ls).
    by apply:   (BZpsS_lcm xs gs).
  move /BZps_iP: (xs)=> [xp xnz]; move: (BZp_sBZ xp) => xz.
  move /BZps_iP: (ys)=> [yp ynz]; move: (BZp_sBZ yp) => yz.
  move /BZps_iP: (g1s)=> [g1p g1nz]; move: (BZp_sBZ g1p) => g1z.
  move: (BZ_Bezout_cofactors xz yz (or_introl (y <> \0z) xnz)). 
  move: (ZpS_quo xp g1p) (ZpS_quo yp g1p).
  rewrite (proj33 (BZlcm_prop1 xz yz)).
  move: (BZgcd_div xz yz) => [].
  set a := (x %/z BZgcd x y); set b := (y %/z BZgcd x y); set g := BZgcd x y.
  move => e1 e2 az bz; rewrite e1 e2.
  have ap:  inc a BZps. 
    by apply/BZps_iP; split => // aez; case: xnz; rewrite e1 aez BZprod_0r.
  have bp: inc b BZps. 
    by apply/BZps_iP; split => // aez; case: ynz; rewrite e2 aez BZprod_0r.
  by apply: h.
move => a b g z azp bzp gzp zzp bzt.
set t := BZgcd g z.
move: (BZpsS_gcd gzp zzp); rewrite -/t => /BZps_iP [tp tnz].
move: (BZps_sBZ gzp)  (BZp_sBZ tp) => gz tz.
move: (BZps_sBZ azp)(BZps_sBZ bzp)(BZps_sBZ zzp) => az bz zz.
move /BZps_iP: gzp => [gp gnz]; move /BZps_iP: azp => [ap anz].
move /BZps_iP: bzp => [_ bnz]; move: (ZSp az bz)  => abz.
move: (ZSp gz az) (ZS_gcd (ZSp gz bz) zz) => pa pb.
move: (BZgcd_div gz zz).
move: (BZ_Bezout_cofactors  gz zz (or_introl (z <> \0z) gnz)).
set g' := (g %/z t); set z' := (z %/z t); move => bz1 [eq1 eq2].
move: (ZS_quo gz tz) (ZS_quo zz tz); rewrite -/g' -/z'; move => g'z z'z.
move: (ZSp abz  g'z) => abgz.
move: (ZS_gcd z'z bz) => gs1.
have ->: BZgcd z ((a *z b) *z g) =  t *z BZgcd z' ((a *z b) *z g').
  rewrite eq1 {1} eq2 -/t (BZprodC _ g').
  rewrite  (BZprodA abz g'z tz) (BZprodC _ t).
  rewrite (BZgcd_prodD z'z  abgz tp); reflexivity.
have cp1:BZcoprime z' g' 
   by rewrite /BZcoprime BZgcd_C;apply: (BZ_coprime_if_Bezout g'z z'z bz1).
have ->: BZgcd z' ((a *z b) *z g') =  BZgcd z' ((a *z b)).
   rewrite BZprodC; apply: (BZgcd_simp z'z g'z abz cp1).
move: (BZlcm_prop1 pa pb) => [_ _ ->].
have ->: BZgcd (g *z a) (BZgcd (g *z b) z) = t.
  rewrite /t (BZgcd_A (ZSp gz az)(ZSp gz bz) zz).
  rewrite (BZgcd_prodD az bz gp).
  move: (BZ_coprime_if_Bezout az bz bzt); rewrite /BZcoprime => ->.
  by rewrite (BZprod_1r gz).
have ->: ((g *z a) %/z t) = g' *z a.
  rewrite eq1 -/t.
  rewrite - (BZprodA tz (ZS_quo gz tz) az). 
  by rewrite (BZdvds_pr5 tz  (ZSp  g'z az) tnz).
have ->: (BZgcd (g *z b) z %/z t) = BZgcd z' b.
  move: (ZSp g'z bz) => h.
  rewrite eq2 {1} eq1 -/t - (BZprodA tz g'z bz) (BZgcd_prodD h z'z tp) BZgcd_C.
  by rewrite (BZgcd_simp z'z g'z bz cp1) (BZdvds_pr5 tz gs1 tnz).
suff:  BZgcd z' (a *z b) %|z ((g' *z a) *z BZgcd z' b).
  rewrite  (BZprodC t).
  move: (ZS_gcd z'z abz) (ZSp (ZSp g'z az) (ZS_gcd z'z bz)) => r1 r2.
  by move/ (BZdvds_prod r1 r2 tz tnz).
rewrite - (BZprodA g'z az gs1).
apply: (@BZdvds_trans  (a *z BZgcd z' b)).
  apply: (BZdvds_pr1 g'z (ZSp az gs1)); apply:BZprod_nz => //.
rewrite - (BZgcd_prodD z'z bz ap).
move: (BZgcd_prop3 z'z abz)=> [[p1 p2 _ ] _].
move: (BZgcd_prop3 (ZSp az z'z) abz)=>  [[_ _ p3] _ ].
apply: p3; last by apply: p2.
apply: (@BZdvds_trans z'); [apply: (BZdvds_pr1 az z'z) | exact ].
Qed.


(* Uniqueness of Bezout *)

Lemma Bezout_non_unique1 a b u v: intp a -> intp b ->
   intp u -> intp v -> BZcoprime a b -> (a *z u) +z (b *z v) = \0z ->
   exists q, [/\ intp q, u = q *z b & v = BZopp(q *z a) ].
Proof.
move => az bz uz vz cab eq1.
move:(BZ_Bezout_if_coprime az bz cab)=> [u' [v'[u'z v'z ha]]].
move:(ZSp az uz)(ZSp bz vz) (ZSp az u'z)(ZSp bz v'z)=> auz bvz au'z bv'z.
case: (equal_or_not a \0z) => anz.
  move: ha eq1. 
  rewrite /Bezout_rel anz ! BZprod_0l (BZsum_0l bvz) (BZsum_0l bv'z) => h.
  move: (BZprod_1_inversion_l bz v'z h) => [_ sb] pz.
  have sa: b *z b = \1z. 
    case: sb => ->; first exact (BZprod_1r ZS1). 
    by rewrite (BZprod_m1r ZSm1) BZopp_m1.
  move:(f_equal (fun z => b *z z) pz); rewrite (BZprodA bz bz vz) sa => sc.
  exists (u *z b); split. 
  + by apply:ZSp.
  + by rewrite - (BZprodA uz bz bz) sa (BZprod_1r uz). 
  + by move: sc;rewrite !BZprod_0r BZopp_0 (BZprod_1l vz).
move:(BZdvd_correct vz az anz) => [qz rp [sc sd /BZp_sBZ rz]].
have hc:= ZSp qz bz; have wz := ZSs uz hc; have aqz := ZSp az qz.
move: eq1.
rewrite sc (BZprodDr bz aqz rz) (BZprodC b) - (BZprodA az qz bz). 
rewrite (BZsumA (ZSp az uz) (ZSp az hc) (ZSp bz rz))  - (BZprodDr az uz hc).
move:(BZ_positive_quo_gcd rp az) (proj2 (BZgcd_div az rz)); rewrite BZgcd_C. 
move: (ZSo qz) => nqz qa qb qc.
move: (BZgcd_rem az (ZSp bz rz) wz); rewrite BZsumC qc. 
rewrite (BZgcd_simp az bz rz cab) (BZgcd_zero az) => qd.
have ww: inc (a *z (u +z (v %/z a) *z b)) BZ by apply:ZSp.
case: (equal_or_not (v %%z a) \0z) => erz.
  exists (BZopp (v %/z a)); move:qc.
  rewrite erz  BZprod_0r (BZsum_0r ww) (BZsum_0r aqz) => qc.
  rewrite (BZopp_prod_l nqz az) (BZopp_K qz) (BZprodC a); split => //.
  apply:(BZdiff_diag_rw uz (ZSp nqz bz)). 
  rewrite /BZdiff - (BZopp_prod_l qz bz) (BZopp_K hc); ex_middle wnz.
  by case: (BZprod_nz az wz anz wnz).
move: qa qb; rewrite - qd => qa qb.
have qe: inc ((v %%z a) %/z BZabs a) BZps.
  by apply/BZps_iP; split => // ez; case: erz; rewrite qb ez BZprod_0r.
move: (BZprod_Mpp (BZabs_iN az) qe);rewrite - qb => hh; BZo_tac.
Qed.

Lemma Bezout_non_unique2 a b u v u' v': intp a -> intp b ->
   intp u -> intp v -> intp u' -> intp v' ->
   Bezout_rel a b u v -> Bezout_rel a b u' v' ->
   exists q, [/\ inc q BZ, u' = u +z q *z b & v' = v -z q *z a].
Proof.
move => az bz uz vz u'z v'z eq1 eq2.
have cp: BZcoprime a b by apply: BZ_coprime_if_Bezout => //; exists u,v.
move:(ZSp az uz)(ZSp az u'z)(ZSp bz vz)(ZSp bz v'z)=> auz au'z bvz bv'z.
move: (BZdiff_diag ZS1); rewrite - {1} eq2 - eq1.
rewrite (BZdiff_diff2 (ZSs au'z bv'z) auz bvz).
rewrite /BZdiff  (BZsum_AC au'z bv'z (ZSo auz)).
rewrite - /(BZdiff (a *z u') _) - (BZprodBr az u'z uz).
rewrite - (BZsumA (ZSp az (ZS_diff u'z uz)) bv'z (ZSo bvz)).
rewrite - /(BZdiff _ _) - (BZprodBr bz v'z vz) => H.
move:(Bezout_non_unique1 az bz (ZS_diff u'z uz) (ZS_diff v'z vz) cp H).
by move => [q [qz ha hb]]; exists q; rewrite - ha -hb !BZsum_diff.
Qed.


Definition Bezout_pos a b u v :=
    [/\ intp u, inc v BZp, v <z BZabs a & Bezout_rel a b u v ].

Lemma Bezout_pos_exists a b: intp a -> intp b -> a <> \0z ->
    BZcoprime a b -> exists u v, Bezout_pos a b u v.
Proof.
move => az bz anz /(BZ_Bezout_if_coprime az bz) [u [v [uz vz h]]].
move:(BZdvd_correct vz az anz) => [qz rp [sc sd /BZp_sBZ rz]].
have ha: inc ((v %/z a) *z b) BZ by  apply:ZSp.
have hb:inc (u +z (v %/z a) *z b) BZ by apply: ZSs.
move: h; rewrite /Bezout_rel sc (BZprodDr bz (ZSp az qz) rz) (BZprodC b).
rewrite - (BZprodA az qz bz) (BZsumA (ZSp az uz) (ZSp az ha) (ZSp bz rz)).
rewrite - (BZprodDr az uz ha) => hh.
by exists (u +z (v %/z a) *z b), (v %%z a).
Qed.

Lemma Bezout_pos_unique a b u v u' v': intp a -> intp b ->
   Bezout_pos a b u v  -> Bezout_pos a b u' v' ->
   (u = u' /\ v = v'). 
Proof.
move => az bz [uz vzp ha hb] [u'z v'zp hc hd].
move:(Bezout_non_unique2 az bz uz (BZp_sBZ vzp) u'z (BZp_sBZ v'zp) hb hd). 
move => [q [qz sa]].
move: (ZS_sign a) (ZSa az) (BZp_sBZ v'zp) => saz aaz v'z.
have qa:= (ZSp qz saz); have wz := (ZSo qa).
rewrite (BZabs_sign az) (BZprodA qz saz aaz) /BZdiff.
rewrite (BZopp_prod_l qa aaz) BZsumC; set w := (BZopp _) => eq1.
case/BZ_i2P: (wz) => wp.
  move: (BZsum_Mp (ZSp wz aaz) vzp); rewrite - eq1 => qc.
  move: (BZprod_Mpp (BZabs_iN az) wp); rewrite BZprodC => qd.
  case: (zleNgt (zleT qd qc) hc).
move: (BZopp_negative2 wp); rewrite (BZopp_K qa) => xp.
move:(BZsum_diff_ea (ZSp wz aaz) (BZp_sBZ vzp) eq1). 
rewrite - (BZopp_prod_l qa aaz) /BZdiff (BZopp_K  (ZSp qa aaz)) => eq2.
move: (BZsum_Mp (ZSp qa aaz) v'zp); rewrite BZsumC - eq2 => qd.
case: (equal_or_not (q *z BZsign a) \0z) => wnz; last first.
  move/BZps_iP: (conj xp wnz) => wp'.
  move: (BZprod_Mpp (BZabs_iN az) wp');rewrite BZprodC => qd'.
  case:(zleNgt (zleT qd' qd) ha).
rewrite sa eq2 wnz BZprod_0l (BZsum_0r v'z); case: (equal_or_not q \0z) => eqz.
  by rewrite eqz BZprod_0l (BZsum_0r uz).
move: wnz;case /(BZ_i1P): az.
+ move => az; move: ha; rewrite az BZabs_0 => /zgt0xP vn.
  case:(BZ_di_neg_pos vn vzp).
+ by move/BZsign_pos => ->; rewrite (BZprod_1r qz).
+ move/BZsign_neg => ->; rewrite (BZprod_m1r qz) => h. 
  by case/(BZnon_zero_opp qz):eqz.
Qed.

Lemma Bezout_pos_aux a b u v : intp a -> intp b -> b <> \0z ->
   Bezout_pos a b u v  -> BZabs u <=z BZabs b.
Proof.
move => az bz anz [uz vzp ha hb].
move: (ZSo bz)(BZp_sBZ vzp)  => nbz vz.
move:(zle_triangular ZS1 (ZSp nbz vz)).
have <-: a *z u = \1z +z (BZopp b) *z v. 
  by rewrite - hb -(BZopp_prod_l bz vz);symmetry; apply:BZdiff_sum1; apply: ZSp.
rewrite (BZprod_abs az uz) (BZprod_abs nbz vz) BZabs_opp BZabs_1 => le1.
case: (equal_or_not (BZabs u) \0z) => eauz.
   rewrite eauz; apply/zle0xP; exact: (BZabs_iN bz).
case: (equal_or_not v \0z) => evz.
  have: \1z <=z BZabs b. 
    apply:BZ1_small; apply/BZps_iP;split; first by apply:(BZabs_iN bz).
    by move => hh;move:(BZabs_0p bz hh).
  move:hb;rewrite /Bezout_rel evz BZprod_0r (BZsum_0r (ZSp az uz)).
  by move /(BZprod_1_inversion_s az uz) => ->.
have vsp: inc v BZps by apply/BZps_iP.
move:(ZSa uz)(ZSa vz)(ZSa bz) => auz avz abz.
apply/(BZprod_ple2r auz abz vsp); rewrite BZprodC.
have h: inc (BZabs u) BZps by move/BZps_iP: (conj (BZabs_iN uz) eauz).
move:(zlt_leT (BZprod_Mltgt0 h ha) le1); rewrite BZsumC.
by move/(zlt_succ1P (ZSp vz auz) (ZSp abz avz)); rewrite (BZabs_pos vzp).
Qed.

Lemma Bezout_pos_aux2 a b u v : intp a -> intp b -> b <> \0z ->
    BZabs b <> \1z ->  Bezout_pos a b u v  -> BZabs u <z BZabs b.
Proof.
move => az bz bnz abn1 ha; split; first apply: (Bezout_pos_aux az bz bnz ha).
move: ha => [uz vzp ha hb] sa.
have vz: intp v by BZo_tac. 
move:(ZS_sign u)(ZS_sign b) => su sb.
have aux: inc (a *z BZsign u +z v *z BZsign b) BZ by apply:ZSs; apply: ZSp.
move: hb; rewrite /Bezout_rel (BZabs_sign uz) (BZprodA az su (ZSa uz)).
rewrite (BZprodC b) (BZabs_sign bz) (BZprodA vz sb (ZSa bz)) sa.
have ra := ZSa bz.
rewrite -BZprodDl //; try apply:ZSp => //.
move /(BZprod_1_inversion_s aux (ZSa bz)).
by rewrite BZabs_abs.
Qed.



Definition Ngcd n m := BZ_val (BZgcd (BZ_of_nat n)(BZ_of_nat m)).

Lemma NS_gcd n m: natp n -> natp m -> natp (Ngcd n m).
Proof.
by move => nN mN; apply: BZ_valN; apply:ZS_gcd; apply: BZ_of_nat_i.
Qed.

Lemma Ngcd_C n m: Ngcd n m = Ngcd m n.
Proof. by rewrite /Ngcd BZgcd_C. Qed.

Lemma Ngcd_n1 n: natp n ->  Ngcd n \1c = \1c.
Proof.
by move => nN; rewrite /Ngcd (BZgcd_x1 (BZ_of_nat_i nN)) /BZ_one BZ_of_nat_val.
Qed.

Lemma Ngcd_1n n: natp n ->  Ngcd \1c n = \1c.
Proof. rewrite Ngcd_C; apply: Ngcd_n1. Qed.


Lemma Ngcd_n0 n: natp n ->  Ngcd n \0c = n.
Proof.
move => nN; rewrite /Ngcd (BZgcd_zero (BZ_of_nat_i nN)). 
by rewrite BZabs_val BZ_of_nat_val.
Qed.

Lemma Ngcd_0n n: natp n ->  Ngcd \0c n = n.
Proof. rewrite Ngcd_C; apply: Ngcd_n0. Qed.

Lemma Ngcd_nn n: natp n ->  Ngcd n n = n.
Proof. 
move => nN. 
by rewrite /Ngcd (BZgcd_id (BZ_of_nat_i nN)) BZabs_val BZ_of_nat_val.
Qed.

Lemma Ngcd_div a b (g:= (Ngcd a b)): natp a -> natp b ->
  a = g *c  (a %/c g) /\ b = g *c  (b %/c g).
Proof.
move => aN bN.
move:(BZ_of_nat_i aN)(BZ_of_nat_i bN) => az bz.
move: (BZp_hi_pr (ZpS_gcd az bz))  (BZ_valN (ZS_gcd az bz)) (BZgcd_div az bz).
move => eq hh. set h := (P (BZgcd (BZ_of_nat a) (BZ_of_nat b))).
move: (NS_quo h aN) (NS_quo h bN) => caN cbN.
rewrite - eq (BZquo_cN aN hh) (BZquo_cN bN hh) (BZprod_cN hh caN).
rewrite (BZprod_cN hh cbN); move => [/BZ_of_nat_inj aa /BZ_of_nat_inj bb].
done.
Qed.

Definition Ngcd_prop a b p :=
   [/\ natp p, p %|c a, p %|c b  & 
    forall t, natp t  ->  t %|c a  -> t %|c b  -> t %|c p].

Lemma Ngcd_P a b: natp a -> natp b ->  
   (Ngcd_prop a b (Ngcd a b) 
       /\ forall g,  Ngcd_prop a b g -> (Ngcd a b) = g).
Proof.
move => aN bN.
move:(BZ_of_nat_i aN)(BZ_of_nat_i bN) => az bz.
move:(NS_gcd aN bN) => gN.
have ww: BZ_of_nat (Ngcd a b) = BZgcd (BZ_of_nat a) (BZ_of_nat b).
  apply:(BZp_hi_pr (ZpS_gcd az bz)).
move:(BZgcd_prop3' az bz) => [[ha hb hc hd] he].
have: Ngcd a b %|c a by apply/(BZdiv_cN gN aN); rewrite  ww.
have: Ngcd a b %|c b by apply/(BZdiv_cN gN bN); rewrite  ww. 
have Hp t:  natp t -> t %|c a -> t %|c b -> t %|c Ngcd a b.
   move => tN /(BZdiv_cN tN aN) sa /(BZdiv_cN tN bN) sb.
  by apply /(BZdiv_cN tN gN); rewrite ww; apply:hd => //; apply: BZ_of_natp_i.
split => //  k [ga gb gc gd].
apply/BZ_of_nat_inj; rewrite ww; apply: he; split.
+ by apply: BZ_of_natp_i.
+ by apply/BZdiv_cN.
+ by apply/BZdiv_cN.
+ move => y tp;move:(BZ_valN (BZp_sBZ tp)) => h. 
  move: (BZp_hi_pr tp) => <- /(BZdiv_cN h aN) sa  /(BZdiv_cN h bN) sb.
  by apply /(BZdiv_cN h ga); apply: gd.
Qed.

Lemma Ngcd_nz a b: natp a -> natp b -> 
  Ngcd a b = \0c ->  (a = \0c /\ b = \0c).
Proof. 
by move => az bz h; move: (Ngcd_div az bz); rewrite h !cprod0l. 
Qed.

Lemma Ngcd_nz1 a b: natp a -> natp b-> 
  (a <> \0c \/ b <> \0c) -> Ngcd a b <> \0c.
Proof. 
by move => az bz h gnz; move: (Ngcd_nz az bz gnz) => [a0 b0]; case: h.
Qed.

Lemma Ngcd_rem a b q: natp a ->natp b -> natp q ->
    Ngcd a (b +c a *c q)  = Ngcd a b.
Proof.
move => aN bN qN.
rewrite /Ngcd - (BZsum_cN bN (NS_prod aN qN)) - (BZprod_cN aN qN).
by rewrite BZgcd_rem //; apply: BZ_of_nat_i.
Qed.

Lemma Ngcd_sum a b: natp a -> natp b ->  Ngcd a (a +c b) = Ngcd a b.
Proof.
move => aN bN; rewrite - {2} (cprod1r (CS_nat aN)) csumC.
apply: (Ngcd_rem aN bN NS1).
Qed.

Lemma Ngcd_diff a b: natp a -> natp b -> a <=c b ->
  Ngcd a (b -c a)  = Ngcd a b.
Proof.
move => aN bN le1.
rewrite - {2} (cdiff_pr le1); symmetry; apply:(Ngcd_sum aN (NS_diff a bN)).
Qed.

Definition Ncoprime a b := Ngcd a b = \1c.




Lemma Ngcd_simp a b c: natp a -> natp b -> natp  c ->
   Ncoprime a b -> Ngcd a (b *c c) = Ngcd a c.
Proof.
move => aN bN cN; rewrite /Ncoprime /Ngcd => h.
move:(BZ_of_nat_i aN) (BZ_of_nat_i bN) (BZ_of_nat_i cN) => az bz cz.
move: (BZp_hi_pr (ZpS_gcd az bz)); rewrite h => h1.
by rewrite - (BZprod_cN bN cN) (BZgcd_simp az bz cz) //.
Qed.

Lemma Nbezout a b: natp a -> natp b -> a <> \0c -> Ncoprime a b ->
   exists u v, [/\ natp u, natp v, a *c u = \1c +c b *c v&
      (b <=c \1c \/ u <c b)].
Proof.
move: NS1 => n1 aN bN anz cp.
case: (equal_or_not b \0c) => bnz.
  move:cp; rewrite /Ncoprime bnz (Ngcd_n0 aN) => ->.
  have aux: \0c <=c \1c \/ \1c <c \0c by left; exact:cle_01.
  by exists \1c, \1c; split => //; rewrite (cprod1r CS1) cprod0l(csum0r CS1).
have bnz1: BZ_of_nat b <> \0z by move/BZ_of_nat_inj.
move:(BZ_of_natp_i aN) (BZ_of_natp_i bN) => ap bp.
move: (BZp_sBZ ap)(BZp_sBZ bp) => az bz.
have cp':BZcoprime (BZ_of_nat b) (BZ_of_nat a).
  rewrite /BZcoprime BZgcd_C - (BZp_hi_pr (ZpS_gcd az bz)). 
  by move: cp; rewrite /Ncoprime/Ngcd => ->.
move: (Bezout_pos_exists bz az bnz1 cp') => [v [u [vz uzp us]]].
move:(BZ_valN (BZp_sBZ uzp)) (BZ_valN vz) => uN vN.
move:(BZp_hi_pr uzp) => equ.
rewrite /Bezout_rel -equ (BZprod_cN aN uN) => bb.
have lc: b <=c \1c \/ P u <c b.
  by right; apply /(zlt_cN uN bN); rewrite  equ - (BZabs_pos bp).
case/BZ_i2P: (vz) => vp.
  move:bb; rewrite -(BZp_hi_pr (BZps_sBZp vp)) (BZprod_cN bN vN).
  rewrite (BZsum_cN (NS_prod bN vN)(NS_prod aN uN)).
  have ha:= (CS_prod2 a (P u)); have hb:= (CS_prod2 b (P v)).
  move/BZ_of_nat_inj => eq1. 
  case:(csum_eq1 hb ha eq1) => eq2.
    exists (P u), (P v); split => //;rewrite - eq1 eq2 csum0l // csum0r//.
  move:eq1; rewrite eq2 (csum0r hb) => /(cprod_eq1 (CS_nat bN) (CS_nat vN)). 
  move:(cpred_pr aN anz) => [sa sb] [b1 _].
  have hc: b <=c \1c \/ \1c <c b by rewrite b1; left; fprops.
  exists \1c, (cpred a); split => //.
  by rewrite (cprod1r (CS_nat aN)) b1 (cprod1l (CS_nat sa)) csumC -Nsucc_rw.
have ha:=(BZ_of_nat_i (NS_prod aN uN)).
move:(BZopp_negative2 vp) => ovp.
have:  BZ_of_nat (a *c P u) = \1z -z  BZ_of_nat b *z v.
  by rewrite - bb BZdiff_sum //; apply:ZSp.
rewrite /BZdiff (BZopp_prod_r bz vz) -(BZp_hi_pr ovp) BZopp_val.
rewrite (BZprod_cN bN vN) (BZsum_cN NS1 (NS_prod bN vN)); move/BZ_of_nat_inj. 
by move => h; exists (P u),(P v).
Qed.

Lemma Ncoprime_Sn_fib n: natp n -> Ncoprime (Fib n) (Fib (csucc n)).
Proof.
rewrite /Ncoprime;move:n; apply: Nat_induction.
  by rewrite succ_zero  Fib0 Fib1 (Ngcd_0n NS1).
move => n nN;rewrite Ngcd_C (Fib_rec nN) csumC (Ngcd_sum); fprops.
Qed.

Lemma Ngcd_fib n m: natp n -> natp m -> 
  Ngcd (Fib n) (Fib m) = Fib (Ngcd n m).
Proof.
move => nN mN.
move:(cmax_p1 (CS_nat nN)(CS_nat mN)) => [sa sb].
have kN: natp (cmax n m) by apply:Gmax_E.
move: nN mN sa sb; move:(cmax n m) kN => k kN; move:k kN n m.
apply:Nat_induction.
  by move=> n m _ _ /cle0 -> /cle0 ->; rewrite Fib0 (Ngcd_n0 NS0) Fib0.
move => k kN Hrec n m nN mN le1 le2.
wlog lmn: n m nN mN le1 le2 / m <c n.
  move => H; case: (NleT_ell nN mN); last by apply:H.
    by move => <-; rewrite (Ngcd_nn (NS_Fib nN)) (Ngcd_nn nN).
  by rewrite Ngcd_C (Ngcd_C n); apply:H.
case: (equal_or_not m \0c) => mz.
  by rewrite mz Fib0 (Ngcd_n0 nN) (Ngcd_n0 (NS_Fib nN)).
move: (cdiff_pr (proj1 lmn)) (NS_diff m nN) ; set r := n -c m => eq1 rN.
move: (cpred_pr rN (cdiff_nz lmn)) => [pN pv].
have ha: m <=c k by  apply /(cltSleP kN); exact (clt_leT lmn le1).
have hb: r <=c k. 
   apply /(cltSleP kN); apply: clt_leT le1. 
   by rewrite - eq1 csumC;apply:(csum_M0lt rN mz). 
move: (NS_Fib mN) (NS_Fib rN) =>  fmN frN.
move:(NS_Fib (NS_succ mN))(NS_Fib pN) => fsmN fsrN.
rewrite - eq1 Ngcd_C (Ngcd_C _ m) (Ngcd_sum mN rN) {1} pv (csum_nS _ pN).
rewrite (Fib_add mN pN) csumC - pv (Ngcd_rem fmN (NS_prod fsmN frN) fsrN).
rewrite (Ngcd_simp fmN fsmN frN (Ncoprime_Sn_fib mN)).
apply:(Hrec _ _ mN rN ha hb).
Qed.

End RationalIntegers.
Export  RationalIntegers.
