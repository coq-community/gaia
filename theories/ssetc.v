(** *  Compatibility of Z Q R 
  Copyright INRIA (2014) Marelle Team (Jose Grimm).
*)
(* $Id: ssetc.v,v 1.3 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype order ssrnat ssrint ssralg ssrnum div.
Require Export ssetz ssetq1 ssetq2 ssetr.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module RingCompat.

Import GRing.Theory.

Section Conversions.



Definition BZ_of_Z (n:int) :=
  match n with 
    | Posz p => BZ_of_nat (nat_to_B p)
    | Negz p => BZm_of_nat (nat_to_B p.+1)
end.

Local Open Scope ring_scope.

Lemma BZ_of_Z_inc x: intp (BZ_of_Z x).
Proof. 
case: x; move => p /=. 
  apply:BZ_of_nat_i;apply: nat_to_B_Nat.
  apply:BZm_of_nat_i; apply: NS_succ;apply: nat_to_B_Nat.
Qed.

Lemma positive_non_zero1 p :
  inc (BZ_of_nat (nat_to_B p)) BZp.
Proof. by apply:BZ_of_natp_i; apply:nat_to_B_Nat. Qed.

Lemma positive_non_zero2 p :
  inc (BZm_of_nat (csucc (nat_to_B p))) BZms.
Proof. 
apply: BZm_of_natms_i; first by apply: NS_succ;apply: nat_to_B_Nat. 
apply: succ_nz.
Qed.

Lemma positive_non_zero2bis p :
  inc (BZm_of_nat (nat_to_B p.+1)) BZms.
Proof.  exact: (positive_non_zero2 p). Qed.

Lemma BZ_of_Z_injective x y :  BZ_of_Z x = BZ_of_Z y ->  x = y.
Proof.
case: x; case: y; simpl => n m /= eq.
- by move:(nat_to_B_injective (BZ_of_nat_inj eq)) => ->.
- move: (positive_non_zero1 m) (positive_non_zero2 n); rewrite -eq => pa pb.
  case: (BZ_di_neg_pos pb pa).
- move: (positive_non_zero1 n) (positive_non_zero2 m); rewrite -eq => pa pb.
  case: (BZ_di_neg_pos pb pa).
- have pa: cardinalp (nat_to_B m) by move: (nat_to_B_Nat m) => h; fprops.
  have pb: cardinalp (nat_to_B n) by move: (nat_to_B_Nat n) => h; fprops.
  move:(csucc_inj pa pb  (BZm_of_nat_inj eq)) => eq2.
  by rewrite (nat_to_B_injective eq2).
Qed.

Lemma BZ_of_Zp_surjective x : inc x BZp -> exists y:nat, BZ_of_Z y = x.
Proof.
move => pa.
rewrite - (BZp_hi_pr pa).
move /indexed_P: pa => [_ pc _]. 
move: (nat_to_B_surjective pc) => [n ->]; by exists n.
Qed.

Lemma BZ_of_Z_surjective x : intp x -> exists y, BZ_of_Z y = x.
Proof.
case /BZ_i0P => pa.
  move: (BZms_hi_pr pa) => [_ <- ].
  move /indexed_P: pa => [_ pc _]; move/setC1_P: pc => [pB pnz].
  move: (cpred_pr pB pnz) => []; set c := cpred _ => ca ->.
  by move: (nat_to_B_surjective ca) => [n ->];exists (Negz n).
by move/ BZ_of_Zp_surjective: pa => [y ya]; exists y.
Qed.

Fact nonempty_int: inhabited int.
Proof. exact (inhabits 0). Qed.

Definition Z_of_BZ x :=  (chooseT (fun y => BZ_of_Z y = x) nonempty_int).


Lemma Z_of_BZ_pa x: intp x -> (BZ_of_Z (Z_of_BZ x)) = x.
Proof. move => H; exact:(chooseT_pr nonempty_int (BZ_of_Z_surjective H)). Qed.


Lemma Z_of_BZ_pb p : Z_of_BZ (BZ_of_Z p) = p.
Proof. exact: (BZ_of_Z_injective (Z_of_BZ_pa (BZ_of_Z_inc p))). Qed.


Lemma BZ_Z_0: BZ_of_Z 0 = \0z.  Proof. trivial. Qed.
Lemma BZ_Z_1: BZ_of_Z 1%Z = \1z.  
Proof. by simpl; rewrite succ_zero. Qed.

Lemma BZ_Z_1n: BZ_of_Z 1%N = \1z.  
Proof. apply:BZ_Z_1. Qed.

Lemma BZ_Z_m1: BZ_of_Z (- 1%:Z) = \1mz.
Proof. by simpl; rewrite succ_zero. Qed.

Lemma Z_of_BZ_zero: Z_of_BZ \0z = 0%Z.
Proof. by apply:BZ_of_Z_injective; rewrite (Z_of_BZ_pa ZS0)  BZ_Z_0. Qed.

Lemma Z_of_BZ_one: Z_of_BZ \1z = 1%Z.
Proof. by apply:BZ_of_Z_injective; rewrite (Z_of_BZ_pa ZS1)  BZ_Z_1.  Qed.

Lemma Z_of_BZ_mone: Z_of_BZ \1mz = (-1)%Z.
Proof. by apply:BZ_of_Z_injective; rewrite (Z_of_BZ_pa ZSm1) BZ_Z_m1. Qed.

Lemma BZ_of_Z_opp x: BZ_of_Z (- x) = BZopp (BZ_of_Z x).
Proof.
case: x => p; simpl; last by rewrite BZopp_m //.
by rewrite BZopp_p; case: p => //=; rewrite /BZm_of_nat; Ytac0.
Qed.

Lemma BZ_of_Z_neg p: BZ_of_Z (Negz p) = BZopp (BZ_of_Z (Posz p.+1)).
Proof.
by rewrite /= /BZopp /BZ_of_nat/int_np; aw; Ytac0.
Qed.

Lemma BZ_of_Z_abs x: BZ_of_Z (`|x|) = BZabs (BZ_of_Z x).
Proof.
case: x; simpl => p.  
  by rewrite  BZabs_pos //; apply:(positive_non_zero1 p).
move: (@succ_nz (nat_to_B p)) => snz.
by rewrite /BZm_of_nat /BZabs; Ytac0;aw.
Qed.

Lemma BZ_of_Z_sign (x:int): BZ_of_Z (Num.sg x) = BZsign (BZ_of_Z x).
Proof.
case: x => /= p.
  rewrite sgrEz;case: p => /=; first  by rewrite BZsign_0.
  move => p; rewrite (BZsign_pos) ? succ_zero //. 
  apply/BZps_iP; split.
    apply: BZ_of_natp_i; apply: NS_succ; apply: nat_to_B_Nat.
  move=> h; move: (f_equal P h); rewrite BZ_of_nat_val BZ0_val;apply: succ_nz.
rewrite (BZsign_neg (positive_non_zero2 p)) succ_zero //.
Qed.


Lemma BZ_of_Z_prod x y: BZ_of_Z (x * y) = (BZ_of_Z x) *z (BZ_of_Z y). 
Proof.
have ppc:forall n m: nat, BZ_of_Z (Posz n * Posz m) = BZ_of_Z n *z BZ_of_Z m.
 move => n m; move: (positive_non_zero1 n)(positive_non_zero1 m) => pa pb.
 by simpl;rewrite (BZprod_pp pa pb) !BZ_of_nat_val nat_to_B_prod.
have npc: forall n (m:nat), BZ_of_Z (Posz m * Negz n) =
    BZ_of_Z m *z BZ_of_Z (Negz n).
  move => n m; rewrite BZ_of_Z_neg - BZopp_prod_r;try apply:BZ_of_Z_inc.
  by rewrite - ppc NegzE mulrN BZ_of_Z_opp.
move; case: x; case: y => n m.
- by apply: ppc.
- apply: npc.    
- rewrite BZprodC mulrC; apply: npc.
- move:  (positive_non_zero2bis n)(positive_non_zero2bis m) => pa pb.
  rewrite (BZprod_mm pb pa) ! BZm_of_nat_val - nat_to_B_prod //.
Qed.

Lemma BZ_of_Z_succ (x:int): BZ_of_Z (1 + x) = \1z +z BZ_of_Z x.
Proof.
have cp:forall (n: nat), BZ_of_Z (1 + (Posz n)) = \1z +z BZ_of_Z n.
  move => n.
  have pa: cardinalp (nat_to_B n) by move: (nat_to_B_Nat n) => h; fprops.
  simpl; rewrite (BZsum_pp (BZps_sBZp ZpsS1) (positive_non_zero1 n)).
  rewrite 2!BZ_of_nat_val csumC csucc_pr4 //.
case: x=> // n.
rewrite BZ_of_Z_neg NegzE.
have ->: Posz(n.+1)  = 1 + Posz n by [].
have nz := (BZ_of_Z_inc n).
rewrite cp (BZoppD ZS1 nz) (BZsumA ZS1 (ZSo ZS1) (ZSo nz)).
rewrite (BZsum_opp_r ZS1) (BZsum_0l (ZSo nz)) - BZ_of_Z_opp opprD.
by rewrite - {1} (opprK 1) addKr. 
Qed.

Lemma BZ_of_Z_sum (x y: int): BZ_of_Z (x + y) = (BZ_of_Z x) +z (BZ_of_Z y). 
Proof.
move: x y; apply: int_rec.
   move => y; rewrite add0r /= BZsum_0l //; apply:BZ_of_Z_inc. 
move => n Hrec y. 
  have ->: BZ_of_Z n.+1  = (BZ_of_Z n) +z \1z by rewrite BZsumC - BZ_of_Z_succ. 
  have ->: (Posz(n.+1) + y)  = 1 + (Posz n + y) by rewrite addrA; congr (_ + _).
  have z1 := ZS1.
  rewrite BZ_of_Z_succ (BZsumC _ \1z).
  rewrite  - BZsumA ? Hrec //; apply: BZ_of_Z_inc.
move => n Hrec y.
have nz := (BZ_of_Z_inc n).
have ynz := (BZ_of_Z_inc (y-1)).
rewrite addrC - opprB (BZ_of_Z_opp n.+1).
have ->: (Posz(n.+1) - y)  = 1 + (Posz n - y) by rewrite addrA; congr (_ + _).
have ->: Posz(n.+1)  = 1 + Posz n  by [].
have aux : y = 1 + (y - 1) by rewrite addrC (subrK 1 y).
rewrite opprD opprB addrC (addrC y) - addrA Hrec.
rewrite {2} aux  BZ_of_Z_opp 2! BZ_of_Z_succ  (BZoppD ZS1 nz). 
rewrite (BZsum_ACA (ZSo ZS1) (ZSo nz) ZS1 ynz).
rewrite (BZsum_opp_l ZS1) BZsum_0l //; apply: (ZSs (ZSo nz) ynz).
Qed.


Lemma BZ_of_Z_diff x y: BZ_of_Z (x - y) = (BZ_of_Z x) -z (BZ_of_Z y). 
Proof. rewrite BZ_of_Z_sum BZ_of_Z_opp //. Qed.

Lemma BZ_of_Z_pred (x:int): BZ_of_Z (x -1) =  BZ_of_Z x -z \1z.
Proof. by rewrite BZ_of_Z_diff BZ_Z_1. Qed.

Lemma BZ_of_Z_le (x y: int):  x <= y <-> ( (BZ_of_Z x) <=z (BZ_of_Z y)). 
Proof.
have aux: forall (z:int), inc (BZ_of_Z z) BZp <-> 0 <= z.
  case => n. 
    rewrite le0z_nat; split => // _; exact (positive_non_zero1 n).
  split => h.
    by move: (BZ_di_neg_pos (positive_non_zero2 n) h).
  discriminate h.
apply: iff_sym.
apply: (iff_trans (zle_diffP (BZ_of_Z_inc x) (BZ_of_Z_inc y))).
by rewrite - BZ_of_Z_diff - Num.Theory.subr_ge0.
Qed.

Lemma BZ_of_Z_lt (x y:int):  x < y  <-> ( (BZ_of_Z x) <z (BZ_of_Z y)). 
Proof.
rewrite Order.POrderTheory.lt_neqAle; split=> //.
  move/andP => [p1 /BZ_of_Z_le p2]; split => // eq.
  by move /eqP: p1; case; apply:BZ_of_Z_injective.
case; move /BZ_of_Z_le => p1 p2; apply /andP; split => //. 
by apply /eqP => eq; case: p2; rewrite eq.
Qed.

Lemma BZ_of_div (a b:nat): a %| b <-> (BZ_of_Z a) %|z (BZ_of_Z b). 
Proof.
move: (nat_to_B_Nat a) (nat_to_B_Nat b) => aN bN.
move:(BZdiv_cN aN bN) => H.
split => dvd.
  apply/H; move/dvdnP:dvd => [k ->].
  rewrite nat_to_B_prod cprodC; apply: cdivides_pr1 => //.
  apply:nat_to_B_Nat.
move/H: dvd => / cdivides_pr.
move: (NS_quo (nat_to_B a) bN) => /nat_to_B_surjective [k ->].
rewrite -nat_to_B_prod => /nat_to_B_injective ->.  
by apply/dvdnP; exists k; rewrite mulnC.
Qed.


Lemma BZ_of_gcd (n m: nat) : 
  BZgcd (BZ_of_Z n) (BZ_of_Z m) = BZ_of_Z (gcdn n m).
Proof.
move: (dvdn_gcdr m n) (dvdn_gcdr n m); rewrite gcdnC => sa sb.
have sc: forall p,  (p %| n) -> (p %| m) -> p %| gcdn n m.
  by move => p s1 s2; rewrite dvdn_gcd s1 s2.
have pa: inc (BZ_of_Z n) BZ by apply: BZ_of_Z_inc.
have pb: inc (BZ_of_Z m) BZ by apply: BZ_of_Z_inc.
apply: (proj2(BZgcd_prop3' pa pb));split => //. 
+ apply:positive_non_zero1.
+ by apply /BZ_of_div. 
+ by apply /BZ_of_div. 
move => w / BZ_of_Zp_surjective [t <-].
by move/BZ_of_div => ha /BZ_of_div hb; apply/BZ_of_div ; apply: sc.
Qed.


Lemma BZ_of_coprime (n m: nat) : 
  BZcoprime (BZ_of_Z n) (BZ_of_Z m) <-> (div.coprime n m).
Proof.
rewrite /div.coprime /BZcoprime BZ_of_gcd - BZ_Z_1n; split.
  by move/BZ_of_Z_injective;case; move => ->. 
by move /eqP => ->. 
Qed.

Lemma BQopp_compatZ x: BQopp (BQ_of_Z x) = BQ_of_Z (BZopp x).
Proof. by rewrite /BQopp /BZ_of_Z /BQ_of_Z;aw. Qed.


End Conversions.

End RingCompat.
