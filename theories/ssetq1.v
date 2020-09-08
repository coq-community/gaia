(** * The set Q of rational numbers, part 1
  Copyright INRIA (2013-2014) Marelle Team (Jose Grimm).
*)
(* $Id: ssetq1.v,v 1.4 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Require Export sset10 ssetz.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module RationalNumbers.
(** ** The set of rational numbers *)

Notation Qnum := P (only parsing).
Notation Qden := Q  (only parsing).
Definition BQ := Zo (BZ \times BZps) (fun z => BZcoprime (Qnum z) (Qden z)).

Definition BQms:= Zo BQ (fun z => inc (Qnum z) BZms).
Definition BQps:= Zo BQ (fun z => inc (Qnum z) BZps).
Definition BQp:= Zo BQ (fun z => inc (Qnum z) BZp).
Definition BQm:= Zo BQ (fun z => inc (Qnum z) BZm).

Definition ratp x := inc x BQ.

Lemma BQ_P q: ratp q <-> 
  [/\ pairp q, intp (Qnum q), inc (Qden q) BZps 
    & BZcoprime (Qnum q) (Qden q)].
Proof. 
split. 
  by move /Zo_P => [/setX_P [pq Pq Qq] cp]; split.
by move => [pa Pq Qq cp]; apply:Zo_i => //; apply/setX_P.
Qed.

Lemma BQp_sBQ : sub BQp BQ.       Proof. apply: Zo_S. Qed.
Lemma BQps_sBQ : sub BQps BQ.     Proof. apply: Zo_S. Qed.
Lemma BQms_sBQ : sub BQms BQ.     Proof. apply: Zo_S. Qed.
Lemma BQm_sBQ : sub BQm BQ.       Proof. apply: Zo_S. Qed.
Lemma BQps_sBQp : sub BQps BQp.
Proof. by move => t /Zo_P [tQ /BZps_sBZp nt]; apply:Zo_i. Qed.
Lemma BQms_sBQm : sub BQms BQm.
Proof. by move => t /Zo_P [tQ /BZms_sBZm nt]; apply:Zo_i. Qed.

Lemma BQ_of_pair_prop1 a b
   (a' := a %/z (BZgcd a b)) (b' := b %/z (BZgcd a b)):
   intp a  -> inc b BZps ->
  [/\ intp a', inc b' BZps, BZcoprime a' b' & BZBezout a' b'].
Proof.
move => az bzps.
have bz:=(BZps_sBZ bzps).
have bzp:=(BZps_sBZp bzps).
have bnz:= (BZps_nz bzps).
have hz: (a <> \0z \/ b <> \0z) by right.
move:(BZ_positive_quo_gcd bzp az) (BZ_nz_quo_gcd bz az bnz).
rewrite BZgcd_C => qp qnz.
have b'zps: inc b' BZps by apply/BZps_iP.
have a'zp:=(ZS_quo az (ZS_gcd az bz)).
have bez:=(BZ_Bezout_cofactors az bz hz).
by split => //; apply: BZ_coprime_if_Bezout => //; apply: BZps_sBZ.
Qed.

Lemma BQ_of_pair_prop2 a b c d:
  intp a -> inc b BZps -> intp c -> inc d BZps ->
  BZBezout a b ->  BZBezout c d -> 
  a *z d = b *z c -> a = c /\ b = d.
Proof.
move => az bzp cz dzp b1 b2 eq1.
have dz := (BZps_sBZ dzp).
have bz:= (BZps_sBZ bzp).
have bnz:= (BZps_nz bzp).
have dnz:= (BZps_nz dzp).
have lbd: gle BZdvdorder b d.
  apply/BZdvdorder_gle; split => //.
  have [u [v [uz vz eq2]]]:= b1.
  have auz:= ZSp az uz.
  have avz:= ZSp bz vz.
  have cuz:= ZSp cz uz.
  have dvz:= ZSp dz vz.
  move: (BZprod_1r dz); rewrite - eq2 BZprodDr // BZprodA // (BZprodC d) eq1.
  rewrite (BZprodC b v) BZprodA // - BZprodA // (BZprodC b) - BZprodDl // => <-.
  by apply:BZdvds_pr1 => //; apply: ZSs.
have ldb: gle BZdvdorder d b.
  apply/BZdvdorder_gle; split => //.
  have [u [v [uz vz eq2]]] := b2.
  have auz:=ZSp az uz.
  have avz := ZSp az vz.
  have cuz:= ZSp cz uz.
  have dvz:= ZSp dz vz.
  have bvz:= ZSp bz vz.
  move: (BZprod_1r bz); rewrite -eq2 BZprodDr// BZprodA// -eq1 (BZprodC _ d). 
  rewrite - BZprodA// (BZprodC d) (BZprodC d) BZprodA// -  BZprodDl// => <-.
  by apply:BZdvds_pr1 => //; apply: ZSs.
have ebd:= (order_antisymmetry (proj1 BZdvd_lattice) lbd ldb).
by move: eq1; rewrite ebd BZprodC;move/ (BZprod_eq2l az cz dz dnz).
Qed.

Lemma BQ_of_pair_prop3 a b c d
   (a' := a %/z (BZgcd a b)) (b' := b %/z (BZgcd a b))
   (c' := c %/z (BZgcd c d)) (d' := d %/z (BZgcd c d)):
   intp a -> inc b BZps -> intp c -> inc d BZps ->
   (a *z d = b *z c <-> (a' = c' /\ b' = d')).  
Proof.
move => az bzps cz dzps.
move:(BZps_sBZ bzps) (BZps_sBZ dzps) => bz dz.
move: (BQ_of_pair_prop1 az bzps) (BQ_of_pair_prop1 cz dzps).
rewrite -/a' -/b' -/c' -/d'; move => [a'z b'zps cp1 be1] [c'z d'zps cp2 be2].
move:(BZgcd_div az bz) => [ {3} -> {3} -> ]. 
move:(BZgcd_div cz dz) => [ {3} -> {1} -> ]. 
have pabz:= (ZS_gcd az bz).
have pcdz:= (ZS_gcd cz dz).
have b'z := (BZps_sBZ b'zps).
have d'z :=(BZps_sBZ d'zps). 
have ha := (ZSp pcdz d'z).
have hb:=(ZSp pcdz c'z).
have qa := (ZSp a'z d'z); have qb :=(ZSp b'z c'z).
rewrite -(BZprodA pabz a'z ha) -(BZprodA pabz b'z hb) (BZprodC a') (BZprodC b').
rewrite -(BZprodA pcdz d'z a'z) -(BZprodA pcdz c'z b'z)(BZprodC d')(BZprodC c').
rewrite (BZprodA pabz pcdz qa) (BZprodA pabz pcdz qb).
split; last by move => [-> ->]; rewrite (BZprodC d').
have ppz: intp (BZgcd a b *z BZgcd c d) by apply:ZSp.
have ppnz: (BZgcd a b *z BZgcd c d) <> \0z.
   by apply: BZprod_nz => //; apply:BZgcd_nz1 => //; right; apply:BZps_nz.
move/(BZprod_eq2l qa qb ppz ppnz).
exact:BQ_of_pair_prop2.
Qed.

Definition BQ_of_pair_internal a b :=
   J (a %/z (BZgcd a b)) (b %/z (BZgcd a b)).
Definition BQ_of_pair := locked  BQ_of_pair_internal.

Lemma BQ_of_pair_prop4 a b:
  intp a -> inc b BZps -> ratp (BQ_of_pair a b).
Proof.
move => az bz.
have [qz qp cp _ ] := (BQ_of_pair_prop1 az bz).
rewrite /BQ_of_pair -lock /BQ_of_pair_internal; set b':= (b %/z BZgcd a b).
apply/BQ_P; split => //; aww.
Qed.


Lemma BQ_of_pair_pos a b: inc a BZp -> inc b BZps -> inc (BQ_of_pair a b) BQp.
Proof.
move => azp bzps; move: (BZp_sBZ azp) (BZps_sBZ bzps) => az bz.
apply:Zo_i; first exact: BQ_of_pair_prop4. 
by rewrite /BQ_of_pair -lock /BQ_of_pair_internal pr1_pair; apply :BZ_positive_quo_gcd.
Qed.

Lemma BQ_of_pair_prop5 a b c d:
  intp a -> inc b BZps -> intp c -> inc d BZps ->
   (a *z d = b *z c <-> BQ_of_pair a b = BQ_of_pair c d).
Proof.
move => az bp cz dp.
apply:(iff_trans (BQ_of_pair_prop3 az bp cz dp)); split.
  by move => [e1 e2]; rewrite /BQ_of_pair -lock /BQ_of_pair_internal e1 e2.
rewrite /BQ_of_pair -lock /BQ_of_pair_internal => e1.
split; first exact: (pr1_def e1).
move: (BQ_of_pair_prop1 az bp) => [_ qb _ _].
move: (BQ_of_pair_prop1 cz dp) => [_ qa _ _].
by rewrite -(BZp_hi_pr (BZps_sBZp qb)) -(BZp_hi_pr (BZps_sBZp qa)) (pr2_def e1).
Qed.

Lemma BQ_pr2 q: ratp q -> BQ_of_pair (Qnum q) (Qden q) = q. 
Proof.
move /BQ_P => [pq nz /BZps_sBZ dz cp].
by rewrite /BQ_of_pair -lock /BQ_of_pair_internal cp (BZquo_one nz) (BZquo_one dz) pq.
Qed.

Definition BQ_of_Z x := (J x \1z).
Definition BQ_of_Zinv x := (J \1z x).

Lemma BQ_of_Z_pr0 z:intp z -> BQ_of_Z z = BQ_of_pair z \1z.
Proof.
move => zZ. 
by rewrite /BQ_of_pair -lock /BQ_of_pair_internal (BZ_coprime1r zZ) (BZquo_one zZ) (BZquo_one ZS1).
Qed.

Lemma BQ_of_Zi_pr0 z:intp z -> BQ_of_Zinv z = BQ_of_pair \1z z.
Proof.
move => zz.
by rewrite /BQ_of_pair -lock /BQ_of_pair_internal BZgcd_C (BZ_coprime1r zz) (BZquo_one zz) (BZquo_one ZS1).
Qed.

Lemma BQ_of_Z_iQ z: intp z -> ratp (BQ_of_Z z).
Proof.
move => zz; rewrite(BQ_of_Z_pr0 zz); apply: BQ_of_pair_prop4 => //;apply: ZpsS1.
Qed.

Lemma BQ_of_Z_iQp z: inc z BZp -> inc (BQ_of_Z z) BQp.
Proof.
move => zp.
by apply: Zo_i; [ apply:(BQ_of_Z_iQ (BZp_sBZ zp)) | rewrite /BQ_of_Z; aw].
Qed.

Lemma BQ_of_Z_iQps z: inc z BZps -> inc (BQ_of_Z z) BQps.
Proof.
move => zp.
by apply: Zo_i; [ apply:(BQ_of_Z_iQ (BZps_sBZ zp)) | rewrite /BQ_of_Z; aw].
Qed.

Lemma BQ_of_Z_iQms z: inc z BZms -> inc (BQ_of_Z z) BQms.
Proof.
move => zn.
by apply: Zo_i; [ apply:(BQ_of_Z_iQ (BZms_sBZ zn)) | rewrite /BQ_of_Z; aw].
Qed.

Lemma BQ_of_Z_iQm z: inc z BZm -> inc (BQ_of_Z z) BQm.
Proof.
case: (equal_or_not z \0z) => z0 zm.
  rewrite z0.
  apply:Zo_i; [ apply: BQ_of_Z_iQ; apply:ZS0 | rewrite/BQ_of_Z;aw; apply: ZmS0].
by apply:(BQms_sBQm); apply: BQ_of_Z_iQms; apply/BZms_iP.
Qed.

Lemma BQ_of_Zi_iQps z: inc z BZps -> inc (BQ_of_Zinv z) BQps.
Proof.
move => zp;apply: Zo_i; last by rewrite /BQ_of_Zinv; aw; apply: ZpsS1.
rewrite (BQ_of_Zi_pr0 (BZps_sBZ zp));apply: BQ_of_pair_prop4 => //; apply: ZS1.
Qed.

Lemma BQ_of_Zi_iQ z: inc z BZps -> ratp (BQ_of_Zinv z).
Proof. by move / BQ_of_Zi_iQps /BQps_sBQ. Qed.

Lemma cardinal_Q : cardinal BQ = aleph0.
Proof.
move/infinite_setP: infinite_Nat => icn.
have hb:=  cardinal_BZ.
set f := Lf BQ_of_Z BZ BQ.
apply: cleA.
  move /sub_smaller: BZps_sBZ; rewrite hb => c2.
  have /sub_smaller: sub BQ (BZ \times BZ).
    by move => t /Zo_S /setX_P [pa pb /BZps_sBZ pc]; apply/setX_P.
  by rewrite - cprod2_pr1 - cprod2cl - cprod2cr hb aleph0_pr3.  
have inf: injection f. 
    apply: lf_injective; first by move =>z; exact: BQ_of_Z_iQ. 
    by move => u  v _ _ /pr1_def. 
by move: (inj_source_smaller inf); rewrite /f; aw; rewrite hb.
Qed.

Lemma cardinal_Qps : cardinal BQps = aleph0.
Proof.
apply: cleA.
  by move: (sub_smaller BQps_sBQ); rewrite cardinal_Q.
set f := Lf (fun z => (BQ_of_Z (BZ_of_nat z))) Nats BQps.
have inf :injection f.
  apply:lf_injective; last by move => u  v _ _ /pr1_def /pr1_def.
  move => n /setC1_P [nN nn] /=. 
  move:(BZ_of_natp_i nN) => h1.
  by apply: BQ_of_Z_iQps; apply /BZps_iP; split => // /pr1_def.
by move:  (inj_source_smaller inf); rewrite /f; aw; rewrite cardinal_Nats.
Qed.

Definition BQ_zero := BQ_of_Z \0z.
Definition BQ_one := BQ_of_Z \1z.
Definition BQ_two := BQ_of_Z \2z.
Definition BQ_three :=  BQ_of_Z \3z.
Definition BQ_four := BQ_of_Z \4z.
Definition BQ_mone := BQ_of_Z \1mz.
Definition BQ_half := BQ_of_Zinv \2z.

Notation "\0q" := BQ_zero.
Notation "\1q" := BQ_one.
Notation "\2q" := BQ_two.
Notation "\3q" := BQ_three.
Notation "\4q" := BQ_four.
Notation "\1mq" := BQ_mone.
Notation "\2hq" := BQ_half.

Lemma QS0 : ratp \0q.
Proof. by apply: BQ_of_Z_iQ; apply:ZS0. Qed.
 
Lemma QpS0 : inc \0q BQp.
Proof. 
apply:Zo_i; [ apply: QS0 | rewrite /BQ_zero /BQ_of_Z; aw; apply: ZpS0 ].
Qed.

Lemma QmS0 : inc \0q BQm.
Proof. apply:Zo_i; [ apply: QS0 | rewrite /BQ_zero /BQ_of_Z; aw; apply: ZmS0 ].
Qed.

Lemma QpsS1 : inc \1q BQps.
Proof. apply: BQ_of_Z_iQps; apply: ZpsS1. Qed.

Lemma QS1 : ratp \1q.
Proof. apply /BQps_sBQ; apply:QpsS1. Qed.

Lemma QpsS2 : inc \2q BQps.
Proof.  apply: BQ_of_Z_iQps; apply: ZpsS2. Qed.

Lemma QS2 : ratp \2q.
Proof. apply /BQps_sBQ; apply:QpsS2. Qed.

Lemma QmsSm1 : inc \1mq BQms.
Proof. apply:BQ_of_Z_iQms;apply: ZmsS_m1. Qed.

Lemma QSm1 : ratp \1mq.
Proof. apply /BQms_sBQ; apply:QmsSm1. Qed.

Lemma QpsSh2 : inc \2hq BQps.
Proof. apply: BQ_of_Zi_iQps; apply:ZpsS2. Qed.

Lemma QSh2 : ratp \2hq.
Proof. apply /BQps_sBQ; apply:QpsSh2. Qed.

Lemma BQ2_nz :  \2q <> \0q.
Proof. move /pr1_def => /pr1_def; fprops. Qed.

Lemma QpsS3 : inc BQ_three BQps.
Proof.  
apply: BQ_of_Z_iQps;apply: indexed_pi. 
apply /setC1_P;split; [ apply:NS3 |  apply: succ_nz].
Qed.

Lemma QS3 : ratp \3q.
Proof. apply /BQps_sBQ:QpsS3. Qed.


Lemma QpsS4 : inc \4q BQps.
Proof.  apply: BQ_of_Z_iQps; apply: ZpsS4. Qed.

Lemma QS4 : ratp \4q.
Proof. apply /BQps_sBQ:QpsS4. Qed.

(** We have a partition of Q as Qp and Qms, but there are more such partitions *)
Lemma BQnum0 : Qnum \0q = \0z.
Proof. by rewrite /BQ_zero /BQ_of_Z ; aw. Qed.

Lemma BQden0 : Qden \0q = \1z.
Proof. by  rewrite /BQ_zero /BQ_of_Z ; aw. Qed.

Lemma BQnum0_P q : ratp q -> Qnum q = \0z -> q = \0q.
Proof. 
move => qq n0.
move/BQ_P: (qq) => [_ nz dp cp].
rewrite - (BQ_pr2 qq) /BQ_zero (BQ_of_Z_pr0 ZS0).
apply/ (BQ_of_pair_prop5 nz dp ZS0 ZpsS1).
by rewrite n0 BZprod_0l BZprod_0r.
Qed.

Lemma BQnum0_P1 x: inc x BZps -> (BQ_of_pair \0z x) = \0q.
Proof.
move => xp; move:(BZps_sBZ xp) => xz.
move/BZps_iP: xp => [xp xnz].
rewrite /BQ_of_pair -lock /BQ_of_pair_internal /BQ_zero BZgcd_C BZgcd_zero //.
rewrite (BZabs_pos xp) (proj2 (BZ_quorem00 xz)).
by rewrite/ BQ_of_Z (proj2 (BZdvd_itself xz xnz)).
Qed.

Lemma BQ1_nz: \1q <> \0q.
Proof. by move /pr1_def; apply:BZ1_nz.  Qed.

Lemma BQ_i0P x: ratp x <-> (inc x BQms \/ inc x BQp).
Proof.  
split; last by case => h; [ apply: BQms_sBQ | apply: BQp_sBQ].
move => xq; move /BQ_P: (xq) => [_ /BZ_i0P ha _ _]. 
by case:ha; [left | right];apply: Zo_i.
Qed.

Lemma BQ_i1P x: ratp x  <-> [\/ x = \0q, inc x BQps | inc x BQms].
Proof.
split.
  move => h; move /BQ_P: (h) => [_ /BZ_i1P ha _ _]; case: ha => t.
  + by constructor 1; apply:BQnum0_P.
  + by constructor 2; apply:Zo_i.
  + by constructor 3; apply:Zo_i.
by case; [move => ->; apply: QS0 | apply: BQps_sBQ | apply: BQms_sBQ].
Qed.

Lemma BQ_i2P x: ratp x <-> (inc x BQps \/ inc x BQm).
Proof.
split; last by case => h; [apply: BQps_sBQ | apply: BQm_sBQ].
move => h; move /BQ_P: (h) => [_ /BZ_i2P ha _ _]. 
by case:ha; [left | right];apply: Zo_i.
Qed.

Lemma BQ_di_neg_pos x: inc x BQms -> inc x BQp -> False.
Proof. move => /Zo_hi pa /Zo_hi pb; apply:(BZ_di_neg_pos pa pb). Qed.

Lemma BQ_di_pos_neg x: inc x  BQps -> inc x BQm -> False.
Proof. move => /Zo_hi pa /Zo_hi pb; apply:(BZ_di_pos_neg pa pb). Qed.

Lemma BQ_di_neg_spos x: inc x BQms -> inc x BQps -> False.
Proof. 
move => h; move:(BQms_sBQm h) =>h1 h2; apply:BQ_di_pos_neg h2 h1.
Qed.

Lemma BQms_nz  x: inc x BQms -> x <> \0q.
Proof. 
by move=> /Zo_hi /BZms_iP [_ n0]; dneg x0; rewrite x0 BQnum0.
Qed.

Lemma BQps_nz  x: inc x BQps -> x <> \0q.
Proof. 
by move=> /Zo_hi/BZps_iP [_ n0]; dneg x0; rewrite x0 BQnum0.
Qed.

Lemma BQps_iP x: inc x BQps <-> inc x BQp /\ x <> \0q.
Proof.
split; first by  move => h; split; [ apply:BQps_sBQp | apply: BQps_nz].
move => [ /Zo_P [xq nxp] xnz ]; apply: Zo_i => //. 
by apply/BZps_iP; split => //; move/(BQnum0_P xq).
Qed.

Lemma BQms_iP x: inc x BQms <-> inc x BQm /\ x <> \0q.
Proof.
split; first by move => h; split; [ apply:BQms_sBQm| apply:  BQms_nz]. 
move => [ /Zo_P [xq nxn] xnz ]; apply: Zo_i => //. 
by apply/BZms_iP; split => //; move/(BQnum0_P xq).
Qed.


(** ** Opposite *)

(** The oppositive of a number is obtained by taking the opposite of the 
numerator *)

Definition BQopp x:= J (BZopp (Qnum x)) (Qden x).

Lemma QSo x: ratp x -> ratp (BQopp x).
Proof.
rewrite /BQopp => xq; move/BQ_P: xq => [_ nz dn cp]; apply /BQ_P; aw.
have pc':= (BZps_sBZ dn).
by split; [ fprops | apply:ZSo | exact| rewrite /BZcoprime - BZgcd_opp ].
Qed.


Lemma BQopp_0 : BQopp \0q = \0q.
Proof. by rewrite /BQopp /BQ_zero /BQ_of_Z pr1_pair pr2_pair BZopp_0. Qed.

Lemma BQopp0_bis x: ratp x -> (x = \0q <-> BQopp x = \0q).
Proof. 
move => xq; split => h; first by rewrite h; exact BQopp_0.
apply:(BQnum0_P xq); move/BQ_P:xq => [_ nz _ _].
by rewrite -(BZopp_K nz) (pr1_def h) BZopp_0.
Qed.

(** Oppositive maps Qp to Qm and Qps to Qms. It is an involution of Q  *)

Lemma BQopp_num x: Qnum (BQopp x) = BZopp (Qnum x).
Proof. by rewrite /BQopp; aw. Qed.

Lemma BQopp_den x: Qden (BQopp x) = Qden x.
Proof. by rewrite /BQopp; aw. Qed.


Lemma BQopp_positive1 x: inc x BQps -> inc (BQopp x) BQms.
Proof.
move => /Zo_P [xq xp]; apply/Zo_i; first by apply:QSo.
by rewrite /BQopp; aw;apply/BZopp_positive1. 
Qed.

Lemma BQopp_positive2 x: inc x BQp -> inc (BQopp x) BQm.
Proof.
move => /Zo_P [xq xp]; apply/Zo_i; first by apply: QSo.
by rewrite /BQopp; aw;apply/BZopp_positive2. 
Qed.

Lemma BQopp_negative1 x: inc x BQms -> inc (BQopp x) BQps.
Proof. 
move => /Zo_P [xq xn]; apply/Zo_i; first by apply: QSo.
by rewrite /BQopp; aw;apply/BZopp_negative1. 
Qed.

Lemma BQopp_negative2 x: inc x BQm -> inc (BQopp x) BQp.
Proof. 
move =>  /Zo_P [xq xn]; apply/Zo_i; first by apply: QSo.
by rewrite /BQopp; aw;apply/BZopp_negative2. 
Qed.

Lemma BQopp_K x: ratp x -> BQopp (BQopp x) = x.
Proof. 
by move => /BQ_P [px nx _ _]; rewrite /BQopp pr1_pair pr2_pair (BZopp_K nx).
Qed.

Lemma BQ_of_pair_opp a b: intp a -> inc b BZps ->
   (BQ_of_pair (BZopp a) b)  = BQopp (BQ_of_pair a b). 
Proof.
move => az bzps; move:(BZps_sBZ bzps) => bz.
rewrite /BQ_of_pair -lock /BQ_of_pair_internal /BQopp -(BZgcd_opp az bz); aw.
by rewrite (BZquo_opp2 (BZgcd_div2 az bz)).
Qed.


Lemma BQ_of_pair_neg a b: inc a BZm -> inc b BZps -> inc (BQ_of_pair a b) BQm.
Proof.
move => azn bzps; move: (BZm_sBZ azn) => az.
have ->: (BQ_of_pair a b) = BQopp (BQ_of_pair (BZopp a) b).
  by rewrite - (BQ_of_pair_opp (ZSo az) bzps) (BZopp_K az).
apply:BQopp_positive2; apply:(BQ_of_pair_pos  (BZopp_negative2 azn) bzps). 
Qed.

Lemma BQ_of_pair_zero a b: intp a -> inc b BZps -> 
   (BQ_of_pair a b) = \0q -> a = \0z.
Proof.
rewrite /BQ_of_pair -lock /BQ_of_pair_internal.
move => az bzp /pr1_def h.
by move: (proj1 (BZgcd_div az (BZps_sBZ bzp))); rewrite h BZprod_0r.
Qed.

Lemma BQ_of_pair_spos a b: inc a BZps -> inc b BZps -> 
   inc (BQ_of_pair a b) BQps.
Proof.
move/BZps_iP => [ap an0] bzp; move:(BQ_of_pair_pos ap bzp) => h.
by apply/BQps_iP; split => // /(BQ_of_pair_zero (BZp_sBZ ap) bzp).
Qed.

Lemma BQ_of_pair_sneg a b: inc a BZms -> inc b BZps -> 
   inc (BQ_of_pair a b) BQms.
Proof.
move/BZms_iP => [ap an0] bzp; move:(BQ_of_pair_neg ap bzp) => h.
by apply/BQms_iP; split => // /(BQ_of_pair_zero (BZm_sBZ ap) bzp).
Qed.

Lemma BQopp_inj a b: ratp a -> ratp b -> BQopp a = BQopp b -> a = b.
Proof. 
by move => az bz h;rewrite - (BQopp_K az) h (BQopp_K bz).  
Qed.

Lemma BQopp_fb: bijection (Lf BQopp BQ BQ).
Proof. 
apply: lf_bijective.
- by move => t tz; apply: QSo.
- apply: BQopp_inj.
- by move => y yz; move: (QSo yz)=> yz'; exists (BQopp y) => //;rewrite BQopp_K.
Qed.

Lemma BQopp_perm: inc (Lf BQopp BQ BQ) (permutations BQ).
Proof. 
have h:= BQopp_fb; have h1:= (proj1 (proj1 h)).
apply: Zo_i => //; apply/functionsP; saw.
Qed.

Lemma BQopp_cZ x: BQopp (BQ_of_Z x) = BQ_of_Z (BZopp x).
Proof. by rewrite /BQopp /BQ_of_Z;aw. Qed.

Lemma BQopp_m1: BQopp \1mq = \1q.
Proof. by rewrite /BQ_mone  BQopp_cZ BZopp_m1. Qed.

Lemma BQopp_1: BQopp \1q = \1mq.
Proof.  by rewrite BQopp_cZ BZopp_1. Qed.

(** ** Absolute value *)

(** Absolute value is obtained by taking the absolute value of the numerator
   *)


Definition BQabs x:= J (BZabs (Qnum x)) (Qden x).


Lemma BQabs_num x: Qnum (BQabs x) = BZabs (Qnum x).
Proof. by rewrite /BQabs; aw. Qed.

Lemma BQabs_den x: Qden (BQabs x) = Qden x.
Proof. by rewrite /BQabs; aw. Qed.

Lemma BQabs_abs x: BQabs (BQabs x) = BQabs x.
Proof. by rewrite /BQabs pr1_pair pr2_pair BZabs_abs. Qed.

Lemma BQabs_opp x:  BQabs (BQopp x) = BQabs x.
Proof. by rewrite /BQabs/BQopp pr1_pair pr2_pair BZabs_opp. Qed.

Lemma BQabs_pos x: inc x BQp -> BQabs x = x.
Proof. 
by move => /Zo_P [/BQ_P [pa pb _ _] xp]; rewrite /BQabs (BZabs_pos xp).
Qed.

Lemma BQabs_0 : BQabs \0q = \0q.
Proof. exact: (BQabs_pos QpS0). Qed.

Lemma BQabs_negs x: inc x BQms -> BQabs x = BQopp x.
Proof. 
by move => /Zo_hi xp; rewrite /BQabs (BZabs_neg xp).
Qed.

Lemma BQabs_neg x: inc x BQm -> BQabs x = BQopp x.
Proof. 
case (equal_or_not x \0q) => e1.
  by rewrite e1 BQopp_0 BQabs_0.
by move => h; apply:BQabs_negs; apply /BQms_iP.
Qed.

Lemma QpSa x: ratp x -> inc (BQabs x) BQp.
Proof.
move => xq.
case/BQ_i0P: (xq) => h; last by rewrite (BQabs_pos h).
rewrite (BQabs_negs h); apply: (BQopp_negative2 (BQms_sBQm h)).
Qed.

Lemma QSa x: ratp x -> ratp (BQabs x).
Proof. by move => /QpSa /BQp_sBQ. Qed.

Lemma BQabs_m1: BQabs \1mq = \1q.
Proof. by rewrite (BQabs_negs QmsSm1) BQopp_m1. Qed.

Lemma BQabs_1: BQabs \1q = \1q.
Proof. exact (BQabs_pos (BQps_sBQp QpsS1)). Qed.

Lemma BQabs0_bis x: ratp x ->  (x = \0q <-> BQabs x = \0q).
Proof.
move => pa; split; first by move => ->; rewrite BQabs_0.
move /pr1_def => pb; apply:BQnum0_P => //.
by move/BQ_P:pa =>[_ / BZabs_0p pc _ _]; apply: pc.
Qed.

(** ** Ordering on Q *)
Definition BQle_aux x y := (Qnum x) *z (Qden y) <=z  (Qden x) *z (Qnum y). 
Definition BQ_le x y := [/\ ratp x, ratp y & BQle_aux x y].
Definition BQ_lt x y :=  BQ_le x y /\ x <> y.

Notation "x <=q y" := (BQ_le x y) (at level 60).
Notation "x <q y" := (BQ_lt x y) (at level 60).

Definition BQ_order := graph_on BQle_aux BQ.

Lemma qleR_aux a: ratp a -> BQle_aux a a.
Proof.
move => /BQ_P [_ nz dzp _]; rewrite /BQle_aux BZprodC. 
by apply: zleR; apply:ZSp=> //; apply: BZps_sBZ.
Qed.

Lemma qleR a: ratp a -> a <=q a.
Proof. by move => aq; split => //; apply:qleR_aux. Qed.

Lemma BQle_P x y: gle BQ_order  x y <-> x <=q y.
Proof. by apply:graph_on_P1. Qed.

Lemma BQlt_P x y: glt BQ_order  x y <-> x <q y.
Proof. by split; move => [pa pb]; split => //; apply /BQle_P. Qed.

Lemma qleA x y:  x <=q y -> y <=q x -> x = y.
Proof.
move => [/BQ_P [px nxz dxp cx] /BQ_P[py nyz dyp cy] le1] [_ _ le2].
move: le1 le2; rewrite /BQle_aux (BZprodC (P y))(BZprodC (Q y)) => la lb.
move: (BZ_Bezout_if_coprime nxz (BZps_sBZ dxp) cx) => bx.
move: (BZ_Bezout_if_coprime nyz (BZps_sBZ dyp) cy) => bzy.
move:(zleA la lb) => eq1. 
move: (BQ_of_pair_prop2 nxz dxp nyz dyp bx bzy eq1) => [sc sd].
by apply: pair_exten.
Qed.

Lemma qltP x y: x <q y <->  [/\ ratp x, ratp y & 
  (Qnum x) *z (Qden y) <z  (Qden x) *z (Qnum y) ]. 
Proof.
split.
  move => [[xq yq le1] xny]; split => //; split => //; dneg h.
  apply: qleA; split => //.
  rewrite /BQle_aux in le1.
  rewrite /BQle_aux (BZprodC (Q y)) h BZprodC; apply: zleR; BZo_tac.
by move => [xq yq [le1 lt1]]; split => //; dneg h; rewrite h BZprodC.
Qed.

Lemma qleT y x z:  x <=q y -> y <=q z -> x <=q z.
Proof.
move => [xq yq le1] [_ zq le2]; split => //.
move/BQ_P: xq => [_ pax pbx _].
move/BQ_P: yq => [_ pay pby _].
move/BQ_P: zq => [_ paz pbz _].
have pcx := BZps_sBZ pbx.
have pcy := BZps_sBZ pby.
have pcz := BZps_sBZ pbz.
red in le1; red in le2.
move: (BZprod_Mlege0 (BZps_sBZp pbz) le1).
  rewrite (BZprodC (P x)) - BZprodA // (BZprodC (Q y)) => le3.
move: (BZprod_Mlege0 (BZps_sBZp pbx) le2).
rewrite - BZprodA // - BZprodA // (BZprodC (Q y)).
rewrite(BZprodC (Q z)) BZprodA //  (BZprodC (P y))  (BZprodC _ (Q x)) => le4.
by move/ (BZprod_ple2r (ZSp pax pcz)  (ZSp pcx paz) pby):(zleT le3 le4).
Qed.


Lemma BQor_or: order BQ_order.
Proof.
have ->:BQ_order =  graph_on BQ_le BQ.
  apply: sgraph_exten => //.
      by move => t /Zo_P [] /setX_P [].
    by move => t /Zo_P [] /setX_P [].
  move => u v; split => /graph_on_P1 [pa pb pc]; apply /graph_on_P1 => //.
apply: order_from_rel; split.
- apply: qleT.
- apply:qleA. 
- by move => x y [xQ yQ _]; split; apply:qleR.
Qed.

Lemma BQor_sr: substrate BQ_order = BQ.
Proof. by apply: graph_on_sr => a /qleR_aux. Qed.

Lemma BQor_tor: total_order BQ_order.
Proof.
split; first by apply: BQor_or.
move => x y; rewrite BQor_sr => xq yq.
move/BQ_P: (xq) => [_ pax /BZps_sBZ pbx _].
move/BQ_P: (yq) => [_ pay /BZps_sBZ pby _].
case:(zleT_ee (ZSp pax pby)(ZSp pbx pay)) => h.
   by left; apply/BQle_P. 
by right; apply/BQle_P; split => //; red; rewrite BZprodC (BZprodC (Q y)).
Qed.

Lemma qleNgt a b: a <=q b -> ~ (b <q a).
Proof. by move => lab [lba]; case; apply:qleA. Qed.

Lemma qlt_leT b a c: a <q b -> b <=q c -> a <q c.
Proof. 
move => [lab nab] lbc;split; first apply: (qleT lab lbc).
dneg ac; apply :qleA => //; ue.
Qed.

Lemma qle_ltT b a c: a <=q b -> b <q c -> a <q c.
Proof. 
move => lab [lbc nbc];split; first apply: (qleT lab lbc).
dneg ac;apply :qleA => //; ue.
Qed.

Lemma qlt_ltT b a c: a <q b -> b <q c -> a <q c.
Proof. move => lab [lbc _]; apply:(qlt_leT lab lbc). Qed.

Ltac BQo_tac := match goal with
  | Ha: ?a <=q ?b, Hb: ?b <=q ?c |-  ?a <=q ?c  
     =>  apply: (qleT Ha Hb)
  | Ha: ?a <q  ?b, Hb: ?b <=q ?c |-  ?a <q ?c  
     =>  apply: (qlt_leT Ha Hb)
  | Ha:?a  <=q ?b, Hb: ?b <q ?c |-  ?a <q ?c  
     =>  apply: (qle_ltT Ha Hb)
  | Ha: ?a <q ?b, Hb: ?b <q ?c |-  ?a <q ?c  
     => apply: (qlt_ltT Ha Hb)
  | Ha: ?a <=q ?b, Hb: ?b <q ?a |- _ 
    => case: (qleNgt Ha Hb)
  | Ha: ?x <=q  ?y, Hb: ?y  <=q ?x |- _ 
   => solve [ rewrite (qleA Ha Hb) ; fprops ]
  | Ha: ratp ?x  |- ?x <=q ?x  => apply: (qleR Ha)
  | Ha: ?a  <=q  _ |- ratp ?a =>  exact (proj31 Ha)
  | Ha:  _ <=q ?a |- ratp ?a =>  exact (proj32 Ha)
  | Ha:  ?a <q _ |- ratp ?a => exact (proj31_1 Ha) 
  | Ha:  _ <q ?a |- ratp ?a => exact (proj32_1 Ha) 
  | Ha: ?a <q ?b  |-  ?a <=q ?b => by move: Ha => []  
end.

Lemma qleT_ee a b: ratp a -> ratp b -> a <=q b  \/ b <=q a.
Proof.
move: BQor_tor => [_]; rewrite BQor_sr => h pa pb.
by case: (h _ _ pa pb)=> h1; [left | right]; apply /BQle_P.
Qed.

Lemma qleT_ell a b: ratp a -> ratp b -> [\/ a = b, a <q b | b <q a].
Proof.
move => aq bq; case: (equal_or_not a b); first by constructor 1.
by move => na; case: (qleT_ee aq bq)=> h1; [constructor 2 | constructor 3];
   split => //; apply: nesym.
Qed.

Lemma qleT_el a b: ratp a -> ratp b -> a <=q b  \/ b <q a.
Proof. 
move=> aq bq; case: (qleT_ell aq bq).
- by move=> ->; left; BQo_tac.
- by move => [pa _]; left.
- by right.
Qed.


Lemma BQ_le_pair a b c d:
  intp a -> inc b BZps -> intp c -> inc d BZps ->
  ((BQ_of_pair a b) <=q (BQ_of_pair c d) <-> (a *z d) <=z (b *z c)).
Proof.
move => az bzps cz dzps.
move: (BQ_of_pair_prop4 az bzps)  (BQ_of_pair_prop4 cz dzps).
set x := BQ_of_pair a b; set y := BQ_of_pair c d => xz yz.
have h : x <=q y <-> BQle_aux x y by split => //; case.
apply: (iff_trans h).
rewrite /BQle_aux /x/y/BQ_of_pair - lock /BQ_of_pair_internal; aw.
have bz:=(BZps_sBZ bzps).
have bzp:=(BZps_sBZp bzps).
have bnz:= (BZps_nz bzps).
have hz: (a <> \0z \/ b <> \0z) by right.
have dz:=(BZps_sBZ dzps).
have dzp:=(BZps_sBZp dzps).
have dnz:= (BZps_nz dzps).
have hz': (c <> \0z \/ d <> \0z) by right.
move: (BZgcd_div az bz)(BZgcd_div cz dz).
set a' := a %/z BZgcd a b; set d':= d %/z BZgcd c d.
set b' := b %/z BZgcd a b; set c':= c %/z BZgcd c d.
move =>[av bv][cv dv].
move: (ZpS_gcd az bz) (ZpS_gcd cz dz) => gzp gz'p.
move:(BZp_sBZ  gzp) (BZp_sBZ  gz'p) => gz gz'.
have a'z:=(ZS_quo az gz).
move:(BZ_positive_quo_gcd bzp az) (BZ_nz_quo_gcd bz az bnz).
rewrite BZgcd_C => qp qnz.
have b'zps: inc b' BZps by apply/BZps_iP.
have c'z:=(ZS_quo cz gz').
move:(BZ_positive_quo_gcd dzp cz) (BZ_nz_quo_gcd dz cz dnz).
rewrite BZgcd_C => qp' qnz'.
have d'zps: inc d' BZps by apply/BZps_iP.
rewrite av {2} bv dv {2} cv.
move: (BZps_sBZ b'zps) (BZps_sBZ d'zps) => b'z  d'z.
rewrite (BZprod_ACA gz a'z gz' d'z) (BZprod_ACA gz b'z gz' c'z).
apply: iff_sym. 
set w := (BZgcd a b *z BZgcd c d).
have wp: inc w BZps.
  by apply:ZpsS_prod; apply/BZps_iP; split => //;apply: BZgcd_nz1.
rewrite (BZprodC w) (BZprodC w).
apply: (BZprod_ple2r (ZSp a'z d'z) (ZSp b'z c'z) wp).
Qed.

Lemma qge0xP x:  x <=q \0q <-> inc x BQm.
Proof. 
have H: ratp x -> (BQle_aux x \0q  <->  inc x BQm).
  move => xQ; move:(xQ) => /BQ_P [_ nz dzp _].
  rewrite /BQle_aux  /BQ_zero /BQ_of_Z; aw; rewrite BZprod_0r (BZprod_1r nz).
  apply:(iff_trans (zge0xP _)).
  by split => h; [ apply: Zo_i | move/Zo_hi: h ].
split; first by move => [xz _ x0]; apply /(H xz).
move => pa; move: (BQm_sBQ pa) => pb; split => //; first by apply: QS0.
by apply/(H pb).
Qed.

Lemma qgt0xP x:  x <q \0q <-> inc x BQms.
Proof.
split; first by move => [/qge0xP xq xnz]; apply /BQms_iP.
by move /BQms_iP => [/qge0xP].
Qed.

Lemma qle0xP x: \0q <=q x <-> inc x BQp.
Proof. 
have H: ratp x -> (BQle_aux \0q x <->  inc x BQp).
  move => xQ; move:(xQ) => /BQ_P [_ nz dzp _]. 
  rewrite /BQle_aux  /BQ_zero /BQ_of_Z; aw; rewrite BZprod_0l (BZprod_1l nz).
  apply:(iff_trans (zle0xP _)).
  by split => h; [ apply: Zo_i | move/Zo_hi: h ].
split; first by move => [_ xq xp]; apply /(H xq).
move => pa; move: (BQp_sBQ pa) => pb; split => //; first by apply: QS0.
by apply/(H pb).
Qed.

Lemma qlt0xP x:  \0q <q x <-> inc x BQps.
Proof.
split; first by move => [/qle0xP pa  /nesym pb]; apply /BQps_iP.
by move /BQps_iP => [/qle0xP h /nesym].
Qed.

Lemma qle_par1 x y: inc x BQps -> inc y BQm ->  y <q x.
Proof. move => /qlt0xP ha /qge0xP hb; BQo_tac. Qed.

Lemma qle_par2 x y: inc x BQp -> inc y BQms ->  y <q x.
Proof. move => /qle0xP ha /qgt0xP hb; BQo_tac. Qed.

Lemma qle_par3 x y: inc x BQp -> inc y BQm ->  y <=q x.
Proof. move => /qle0xP ha /qge0xP hb; BQo_tac. Qed.

Lemma qle_cZ a b: intp a -> intp b ->
    (a <=z b <-> BQ_of_Z a <=q BQ_of_Z b).
Proof.
move => az bz.
have aq: ratp (BQ_of_Z a)  by apply: BQ_of_Z_iQ.
have bq: ratp (BQ_of_Z b) by apply: BQ_of_Z_iQ.
rewrite /BQ_le /BQle_aux /BQ_of_Z; aw; rewrite BZprod_1r //BZprod_1l //.
by split => // [] [].
Qed.

Lemma qlt_cZ a b: intp a -> intp b ->
    (a <z b <-> BQ_of_Z a <q BQ_of_Z b).
Proof.
move => az bz; split; move => [ha hb];split.
+ by apply / qle_cZ.
+ by  move/pr1_def.
+ by apply / qle_cZ.
+ by dneg h; rewrite h.
Qed.

Lemma qlt_01:  \0q <q \1q.
Proof.  by apply/ qlt0xP; exact:QpsS1. Qed.

Lemma qlt_12: \1q <q \2q. 
Proof.   
apply/ (qlt_cZ ZS1 ZS2); apply/ (zlt_cN NS1 NS2);exact clt_12.
Qed.

Lemma qlt_24: \2q <q \4q.
Proof. by move /(qlt_cZ ZS2 ZS4):zlt_24. Qed.

Lemma qle_24: \2q <=q \4q.
Proof. exact (proj1 qlt_24). Qed. 


Lemma BQabs_positive b: ratp b -> b <> \0q -> \0q <q (BQabs b).
Proof. 
move => pa pb; apply /qlt0xP.
by apply /BQps_iP;split; [ apply:QpSa |  move/(BQabs0_bis pa) ].
Qed. 


(** Opposite is an order isomorphism from (Q,<) to (Q,>) *)

Lemma qle_opp x y: x <=q y ->  (BQopp y) <=q  (BQopp x).
Proof.
move => [xq yq lexy]; split; try apply: QSo => //.
move/BQ_P: xq => [_ nxz /BZps_sBZ dxz _].
move/BQ_P: yq => [_ nyz /BZps_sBZ dyz _].
rewrite /BQle_aux /BQopp; aw; rewrite - BZopp_prod_l // - BZopp_prod_r //.
by apply: zle_opp; rewrite (BZprodC (Q y)) (BZprodC (P y)). 
Qed.

Lemma qlt_opp x y: x <q y -> (BQopp y) <q (BQopp x).
Proof. 
move => [lxy nxy]; split; first by apply:qle_opp.
by move: lxy => [xq yq _] no; case: nxy; apply:BQopp_inj.
Qed.

Lemma qlt_oppP x y: ratp x -> ratp y ->
   ((BQopp y) <q  (BQopp x) <-> x <q y).
Proof.
move => xq yq; split; last apply: qlt_opp. 
by move => h;move:(qlt_opp h); rewrite ! BQopp_K.
Qed.

Lemma qle_oppP x y: ratp x -> ratp y ->
   ((BQopp y) <=q  (BQopp x) <-> x <=q y).
Proof.
move => xq yq; split; last apply: qle_opp. 
by move => h;move:(qle_opp h); rewrite ! BQopp_K.
Qed.

Lemma BQabs_prop2 x y: ratp x -> ratp y ->
  (BQabs x <q y <->  (BQopp y <q x /\ x <q y)).
Proof.
move => xq yq.
case /BQ_i0P: (xq) => xp.
   rewrite (BQabs_negs xp); move: (qlt_oppP (QSo xq) yq);rewrite (BQopp_K xq).
   move => h;apply:(iff_trans (iff_sym h)); split; last by move => [].
   move => h1; split => //.
   move:(BQms_sBQm xp) => xp'.
   move:(qle_par3 (BQopp_negative2 xp') xp') => h2.
   move/h: h1 => h3; BQo_tac.
rewrite (BQabs_pos xp); split; last by move => [].
move => lxy; split => //; rewrite - (BQopp_K xq); apply: qlt_opp.
have h: BQopp x <=q x by apply:(qle_par3 xp (BQopp_positive2 xp)).
BQo_tac.
Qed.

Lemma BQabs_prop1 x y: ratp x -> ratp y ->
  (BQabs x <=q y <->  (BQopp y <=q x /\ x <=q y)).
Proof.
move => xq yq.
case /BQ_i0P: (xq) => xp.
   rewrite (BQabs_negs xp); move: (qle_oppP (QSo xq) yq);rewrite (BQopp_K xq).
   move => h;apply:(iff_trans (iff_sym h)); split; last by move => [].
   move => h1; split => //.
   move:(BQms_sBQm xp) => xp'.
   move:(qle_par3 (BQopp_negative2 xp') xp') => h2.
   move/h: h1 => h3; BQo_tac.
rewrite (BQabs_pos xp); split; last by move => [].
move => lxy; split => //; rewrite - (BQopp_K xq); apply: qle_opp.
have h: BQopp x <=q x by apply:(qle_par3 xp (BQopp_positive2 xp)).
BQo_tac.
Qed.

Lemma qle_opp_iso:
  order_isomorphism (Lf BQopp BQ BQ) BQ_order (opp_order BQ_order).
Proof. 
move: BQor_or BQor_sr BQopp_fb => or sr bf.
have la: lf_axiom BQopp BQ BQ by move => t tz; apply:QSo.
move: (opp_osr or) => [pa pb].
hnf;rewrite pb; saw; first  by saw.
hnf; aw;move => x y xz yz; rewrite !LfV//; split.
  by move /BQle_P => h; apply /opp_gleP; apply /BQle_P;apply qle_opp.
move  /opp_gleP /BQle_P => h; apply /BQle_P.
by rewrite - (BQopp_K xz) -(BQopp_K yz); apply qle_opp.
Qed.


(** ** Addition *)


Definition BQsum x y:=
  BQ_of_pair ((Qnum x) *z (Qden y) +z (Qden x) *z (Qnum y))
    ((Qden x) *z  (Qden y)).

Notation "x +q y" := (BQsum x y) (at level 50).

Lemma QSs x y: ratp x -> ratp y -> ratp (x +q y).
Proof.
move => /BQ_P [_ nxz dxp _] /BQ_P [_ nyz dyp _].
move: (ZpsS_prod dxp dyp); apply: BQ_of_pair_prop4. 
by apply:ZSs; apply:ZSp => //; apply: BZps_sBZ.
Qed.


Lemma BQsumC x y: x +q y = y +q x.
Proof.
rewrite /BQsum /BQ_of_pair.
rewrite (BZprodC (Q x) (Q y)) (BZprodC (P x) (Q y)) (BZprodC (Q x) (P y)).
by rewrite (BZsumC ( Q y *z P x)).
Qed.

Lemma BQsumA x y z: ratp x -> ratp y -> ratp z ->
  x  +q (y +q z) = (x +q y) +q z.
Proof. 
suff H: forall x y z, ratp x -> ratp y -> ratp z ->  x +q (y +q z) =
   BQ_of_pair  (Qnum x *z Qden y *z Qden z +z 
   Qnum y *z Qden x *z Qden z +z  Qnum z *z Qden y *z Qden x)
   (Qden x *z Qden y *z Qden z). 
  move => xq yq zq; rewrite (BQsumC  (x +q y) z)  H // H //. 
  move /BQ_P: xq => [_ px /BZps_sBZ qx _].
  move /BQ_P: yq => [_ py /BZps_sBZ qy _].
  move /BQ_P: zq => [_ pz /BZps_sBZ qz _].
  apply: f_equal2.
    have ha: inc ((P z *z Q y) *z Q x) BZ by apply:ZSp => //;  apply:ZSp.
    have hb: inc ((P x *z Q y) *z Q z) BZ by apply:ZSp => //;  apply:ZSp.
    have hc: inc ((P y *z Q x) *z Q z) BZ by apply:ZSp => //;  apply:ZSp.
    rewrite BZsumC (BZsumA ha hb hc).
    rewrite - (BZprodA pz qy qx) (BZprodC (Q y)) (BZprodA pz qx qy).
    by rewrite - (BZprodA px qy qz) (BZprodC (Q y)) (BZprodA px qz qy).
  by rewrite (BZprodC (Q x)) - BZprodA // (BZprodC (Q x)) (BZprodC (Q y)).
clear.
move => x y z xq yq zq; move:(QSs yq zq) => yzq.
move /BQ_P: xq => [_ nx dxp _]; move:(BZps_sBZ dxp) => dx.
move /BQ_P: yq => [_ ny dyp _]; move:(BZps_sBZ dyp) => dy.
move /BQ_P: zq => [_ nz dzp _]; move:(BZps_sBZ dzp) => dz.
move /BQ_P: yzq => [_ nyz dyzp _]; move:(BZps_sBZ dyzp) => dyz.
have ha: intp(P x *z Q (y +q z) +z Q x *z P (y +q z)) by apply:ZSs; apply:ZSp. 
have hb:= (ZpsS_prod dxp dyzp).
have hc:
 intp (((P x *z Q y) *z Q z +z (P y *z Q x) *z Q z) +z (P z *z Q y) *z Q x).
 by apply:ZSs; try apply:ZSs;  apply:ZSp => //; apply:ZSp.
have hd:= (ZpsS_prod (ZpsS_prod dxp dyp) dzp).
apply /(BQ_of_pair_prop5 ha hb hc hd).
set A := (P x *z Q (y +q z) +z Q x *z P (y +q z)).
set B := (((P x *z Q y) *z Q z +z (P y *z Q x) *z Q z) +z (P z *z Q y) *z Q x).
have he: intp (Q x *z Q y)  by apply:ZSp.
have hf: intp (Q z *z A) by apply:ZSp.
have hg: intp (P y *z Q z) by apply:ZSp.
have hi: intp (P z *z Q y) by apply:ZSp.
have hj: intp (Q y *z P z) by apply:ZSp.
set u :=(P y *z Q z +z Q y *z P z) ; set v := (Q y *z Q z).
have uz: intp u by apply:ZSs.
have vzps:= (ZpsS_prod dyp dzp).
have vz := (BZps_sBZ vzps).
rewrite BZprodC - BZprodA  // - BZprodA // - BZprodA //; congr (_ *z _).
have ->: B = P x *z v +z Q x *z u.
  move: (ZSp (ZSp nx dy) dz) (ZSp (ZSp ny dx) dz) (ZSp hi dx) => sa sb sc.
  rewrite /B - BZsumA // BZprodA//; apply: f_equal.
  rewrite (BZprodC _ (Q x)) (BZprodC _ (Q x)) - BZprodA // BZprodDr //.
  by rewrite (BZprodC (Q y)).
rewrite BZprodA // /A /BQsum /BQ_of_pair -lock /BQ_of_pair_internal.
rewrite pr1_pair pr2_pair.
move: (BZgcd_s2 uz vz) (BZgcd_div uz vz) .
set p := BZgcd u v;  set u' := (u %/z p); set v' := (v %/z p).
move => [pZ u'Z v'Z].
have ka : intp (v' *z P x) by apply:ZSp.
have kb : intp (u' *z Q x) by apply:ZSp. 
rewrite -/v; move => [-> ->].
rewrite (BZprodC (P x)  (p *z v')) - (BZprodA pZ v'Z nx) (BZprodC  (P x) v').
rewrite (BZprodC (Q x)  (p *z u')) - (BZprodA pZ u'Z dx)  (BZprodC  (Q x) u').
by rewrite - BZprodDr // (BZprodC p) BZprodA //; apply:ZSs.
Qed.

Lemma BQsum_AC x y z: ratp x -> ratp y -> ratp z ->
  (x +q y) +q z = (x +q z) +q y.
Proof.
move => xq yq zq.
by rewrite - (BQsumA xq yq zq) - (BQsumA xq zq yq) (BQsumC y).
Qed.

Lemma BQsum_CA x y z: ratp x -> ratp y -> ratp z ->
  x +q (y +q z) = y +q (x +q z).
Proof.
by move => xz yz zz;rewrite (BQsumA xz yz zz) (BQsumA yz xz zz) (BQsumC x y).
Qed.

Lemma BQsum_ACA a b c d: ratp a -> ratp b -> ratp c -> ratp d ->
    (a +q b) +q (c +q d) = (a +q c) +q (b +q d).
Proof.
move => az bz cz dz; move:(QSs cz dz) (QSs bz dz)=>  cdz bdz.
by rewrite -!BQsumA // (BQsum_CA bz cz dz).
Qed.

Lemma BQsum_same_den x y: ratp x -> ratp y -> Qden x = Qden y ->
  x +q y = BQ_of_pair (Qnum x +z Qnum y) (Qden x).
Proof.
move => /BQ_P [_ nx dxp cp] /BQ_P [_ ny dyp cy] h.
have dx:= (BZps_sBZ dxp).
have dxy := (ZpsS_prod dxp dxp). 
have nxy := (ZSs nx ny).
rewrite /BQsum - h  (BZprodC (Q x)) - BZprodDl //.
apply/(BQ_of_pair_prop5 (ZSp (ZSs nx ny) dx) dxy nxy dxp).
by rewrite - (BZprodA nxy dx dx) BZprodC.
Qed.

Lemma BQsum_cZ x y: intp x -> intp y -> 
  BQ_of_Z x +q  BQ_of_Z y = BQ_of_Z (x +z y).
Proof.
move => xz yz. 
move: (BQ_of_Z_iQ xz) (BQ_of_Z_iQ yz) => x'Q y'Q.
have h: Q (BQ_of_Z x) = Q (BQ_of_Z y) by rewrite  /BQ_of_Z ! pr2_pair.
by rewrite BQsum_same_den // /BQ_of_Z ; aw; rewrite - BQ_of_Z_pr0 //; apply:ZSs.
Qed.

Lemma BQsum_0l x: ratp x -> \0q +q x  = x.
Proof. 
move => xq; move: (xq) => /BQ_P [px nx dx cx]. 
rewrite /BQsum /BQ_zero /BQ_of_Z pr1_pair pr2_pair BZprod_0l (BZprod_1l nx). 
by rewrite (BZprod_1l (BZps_sBZ dx)) (BZsum_0l nx) BQ_pr2.
Qed.

Lemma BQsum_0r x: ratp x -> x +q \0q = x.
Proof. by move => xq;rewrite BQsumC BQsum_0l. Qed.

Lemma BQsum_11 : \1q +q \1q = \2q. 
Proof.  by rewrite (BQsum_cZ ZS1 ZS1) BZsum_11. Qed.

Lemma BQsum_opp_r x: ratp x ->  x +q (BQopp x) = \0q.
Proof. 
move => xq.
move /BQ_P:(xq) => [_ nx dx _ ].
rewrite (BQsum_same_den xq (QSo xq) (esym (BQopp_den x))) /BQopp pr1_pair.
by rewrite BZsum_opp_r // BQnum0_P1. 
Qed.

Lemma BQsum_opp_l x: ratp x -> (BQopp x) +q x = \0q.
Proof. by move => h; rewrite BQsumC BQsum_opp_r. Qed.

Lemma BQsum_opp_rev a b: ratp a -> ratp b -> a +q b = \0q ->
   a = BQopp b.
Proof.
move => aq bq h.
move: (BQsumA aq bq (QSo bq)). 
by rewrite (BQsum_opp_r bq) h (BQsum_0l (QSo bq)) (BQsum_0r aq).
Qed.

Lemma BQoppD x y: ratp x -> ratp y ->
  BQopp (x +q y) = (BQopp x) +q (BQopp y).
Proof. 
move => xq yq.
move: (QSo xq)(QSo yq) => oxq oyq.
symmetry; apply: BQsum_opp_rev; try apply:QSs => //.
rewrite BQsum_ACA // (BQsumC _ y) (BQsum_opp_r yq).
by rewrite (BQsumC _ x) (BQsum_opp_r xq)(BQsum_0l QS0).
Qed.

Lemma QpsS_sum_r x y: inc x BQp -> inc y BQps -> inc (x +q y) BQps.
Proof. 
move => /Zo_P  [/BQ_P [_ _ pc _] pa] /Zo_P [/BQ_P [_ _ qc _] qa].
move:(ZpsS_prod pc qc) => dp.
apply:BQ_of_pair_spos => //; apply:ZpsS_sum_r; last by apply:ZpsS_prod.
by apply:ZpS_prod => //; apply: BZps_sBZp.
Qed.

Lemma QpS_sum x y: inc x BQp -> inc y BQp -> inc (x +q y) BQp.
Proof. 
move => pa pb; case (equal_or_not y \0q) => h. 
  by rewrite h BQsum_0r //; apply:(BQp_sBQ pa).
by apply:BQps_sBQp; apply:QpsS_sum_r => //;  apply/BQps_iP.
Qed.

Lemma QpsS_sum_l x y: inc x BQps -> inc y BQp ->  inc (x +q y) BQps.
Proof. by move => pa pb; rewrite BQsumC; apply QpsS_sum_r.  Qed.

Lemma QpsS_sum_rl x y: inc x BQps -> inc y BQps -> inc (x +q y) BQps.
Proof. move => pa pb; apply: QpsS_sum_r => //;apply:(BQps_sBQp pa). Qed.

Lemma QmsS_sum_rl x y: inc x BQms -> inc y BQms -> inc (x +q y) BQms.
Proof.
move => xqm yqm.
move: (BQopp_negative1 xqm) (BQopp_negative1 yqm) => xz1 yz1.
move: (BQms_sBQ xqm)(BQms_sBQ yqm) => xq yq.
move:(QpsS_sum_rl xz1 yz1); rewrite - (BQoppD xq yq) => h.
by move: (BQopp_K (QSs xq yq)) => <-; apply: BQopp_positive1.
Qed.

Lemma QmsS_sum_r x y: inc x BQm -> inc y BQms ->  inc (x +q y) BQms.
Proof. 
move => pa pb;case: (equal_or_not x \0q) => h. 
   by rewrite h (BQsum_0l (BQms_sBQ pb)).
by apply:QmsS_sum_rl => //; apply/BQms_iP.
Qed.

Lemma QmsS_sum_l x y: inc x BQms -> inc y BQm -> inc (x +q y) BQms.
Proof. by move => pa pb; rewrite BQsumC; apply: QmsS_sum_r. Qed.

Lemma QmS_sum x y: inc x BQm -> inc y BQm -> inc (x +q y) BQm.
Proof.
move => pa pb;case: (equal_or_not x \0q) => h.
  by rewrite h (BQsum_0l (BQm_sBQ pb)).
by apply:BQms_sBQm; apply:QmsS_sum_l => //;  apply/BQms_iP.
Qed.

(** ** subtraction *)

Definition BQdiff x y := x +q (BQopp y).

Notation "x -q y" := (BQdiff x y) (at level 50).

Lemma QS_diff x y: ratp x -> ratp y -> ratp (x -q y).
Proof. by move => sa /QSo sb; apply:QSs. Qed.

Section BQdiffProps.
Variables (x y z: Set).
Hypotheses (xq: ratp x)(yq: ratp y)(zq: ratp z).

Lemma BQdiff_sum:  (x +q y) -q x = y.
Proof. 
by rewrite /BQdiff BQsumC (BQsumA (QSo xq) xq yq) BQsum_opp_l // BQsum_0l.
Qed.

Lemma BQdiff_sum1:  (y +q x)  -q x = y.
Proof. by rewrite (BQsumC y) BQdiff_sum. Qed.

Lemma BQsum_diff: x +q (y -q x) = y.
Proof. 
by rewrite /BQdiff (BQsumC y) (BQsumA xq (QSo xq) yq) BQsum_opp_r // BQsum_0l. 
Qed.

Lemma BQsum_diff1: (y -q x) +q x = y.
Proof. by rewrite (BQsumC) BQsum_diff. Qed.


Lemma BQdiff_xx :  x -q x = \0q.
Proof. exact: BQsum_opp_r. Qed.

Lemma BQdiff_0r: x -q \0q = x.
Proof. by rewrite /BQdiff BQopp_0 BQsum_0r. Qed.

Lemma BQdiff_0l: \0q -q x = BQopp x.
Proof. by rewrite /BQdiff BQsum_0l //; apply: QSo. Qed.

Lemma BQdiff_sum_simpl_l:  (x +q y) -q  (x +q z) = y -q z.
Proof.
rewrite /BQdiff (BQoppD xq zq) (BQsumC x y).
rewrite (BQsumA (QSs yq xq) (QSo xq) (QSo zq)).
by rewrite  -(BQsumA yq xq (QSo xq)); rewrite BQsum_opp_r // BQsum_0r.
Qed.

Lemma BQdiff_sum_comm: (x +q y) -q z = (x -q z) +q y.
Proof. 
by rewrite /BQdiff (BQsumC x y) (BQsumC _ y) - (BQsumA yq xq) //; apply:QSo.
Qed.


Lemma BQoppB: BQopp (x -q y) = y -q x.
Proof.
rewrite /BQdiff (BQoppD xq (QSo yq)). 
by rewrite (BQopp_K yq) BQsumC.
Qed.

End BQdiffProps.

Section BQdiffProps2.
Variables (x y z: Set).
Hypotheses (xq: ratp x)(yq: ratp y)(zq: ratp z).

Lemma BQsum_diff_ea: x = y +q z -> z = x -q y.
Proof. by move => -> ; rewrite BQdiff_sum. Qed.

Lemma BQdiff_xx_rw:  x -q y = \0q -> x = y.
Proof. 
move => h; move:(f_equal (BQsum y) h); rewrite (BQsum_diff yq xq).
by rewrite BQsum_0r.
Qed.

Lemma BQdiff_sum_simpl_r:  (x +q z) -q (y +q z) = x -q y.
Proof. by rewrite (BQsumC x z) (BQsumC y z);  apply: BQdiff_sum_simpl_l. Qed.

Lemma BQsum_eq2r:  x +q z = y +q z -> x = y.
Proof.
move => h; rewrite - (BQdiff_sum zq xq) - (BQdiff_sum zq yq).
by rewrite BQsumC h BQsumC.
Qed.

Lemma BQsum_eq2l:  x +q y = x +q z -> y = z.
Proof.
by move => h; rewrite - (BQdiff_sum xq yq) - (BQdiff_sum xq zq) h.
Qed.

End  BQdiffProps2.


Lemma BQdiff_diff a b c: ratp a -> ratp b -> ratp c ->
   a -q (b -q c)  = (a -q b) +q c.
Proof.
move => aq bq cq; rewrite /BQdiff (BQoppD bq (QSo cq)) (BQopp_K cq) BQsumA //.
by apply:QSo.
Qed.

Lemma BQdiff_diff_simp a b: ratp a -> ratp b ->  a -q (a -q b) = b.
Proof.
by move => aq bq; rewrite (BQdiff_diff aq aq bq) (BQdiff_xx aq) BQsum_0l.
Qed.

Lemma BQdiff_diff2 a b c: ratp a -> ratp b -> ratp c ->
   a -q (b +q c)  = (a -q b) -q c.
Proof.
move => aq bq cq.
by move:(BQdiff_diff aq bq (QSo cq)); rewrite /BQdiff (BQopp_K cq).
Qed.

Lemma BQdiff_cZ x y: intp x -> intp y -> 
  BQ_of_Z x -q  BQ_of_Z y = BQ_of_Z (x -z y).
Proof.
by move => za /ZSo zb; rewrite /BQdiff (BQopp_cZ y) (BQsum_cZ za zb).
Qed.


(** ** Multiplication *)

Definition BQprod x y :=
  BQ_of_pair ((Qnum x) *z (Qnum y)) ((Qden x) *z  (Qden y)).

Notation "x *q y" := (BQprod x y) (at level 40).

Lemma QSp x y: ratp x -> ratp y -> ratp (x *q y).
Proof. 
move => /BQ_P [_ nx dx pd] /BQ_P [_ ny dy qd].
exact: (BQ_of_pair_prop4 (ZSp nx ny) (ZpsS_prod dx dy)).
Qed.

Lemma BQprodC x y: x *q y = y *q x.
Proof. by rewrite /BQprod /BQ_of_pair BZprodC (BZprodC (Q x)). Qed.

Lemma BQprodA x y z: ratp x -> ratp y -> ratp z ->
  x  *q (y *q z) = (x *q y) *q z.
Proof. 
suff H:forall x y z, ratp x -> ratp y -> ratp z ->  x *q (y *q z) =
   BQ_of_pair  (Qnum x *z Qnum y *z Qnum z)
   (Qden x *z Qden y *z Qden z).
  move => xQ yQ zQ; rewrite (BQprodC (x *q y) z) H // H //. 
  move /BQ_P: xQ => [_ px /BZps_sBZ qx _].
  move /BQ_P: yQ => [_ py /BZps_sBZ qy _].
  move /BQ_P: zQ => [_ pz /BZps_sBZ qz _].
  apply: f_equal2.
    by rewrite (BZprodC (P x)) - BZprodA // (BZprodC (P x)) (BZprodC (P y)).
  by rewrite (BZprodC (Q x)) - BZprodA // (BZprodC (Q x)) (BZprodC (Q y)).
clear; move => x y z xQ yQ zQ; move:(QSp yQ zQ) => yzQ.
move /BQ_P: xQ => [_ px qxp _]; move:(BZps_sBZ qxp) => qx.
move /BQ_P: yQ => [_ py qyp _]; move:(BZps_sBZ qyp) => qy.
move /BQ_P: zQ => [_ pz qzp _]; move:(BZps_sBZ qzp) => qz.
move /BQ_P: yzQ => [_ pyz qyzp _]; move:(BZps_sBZ qyzp) => qyz.
have ha: intp (P x *z P (y *q z)) by apply:ZSp.
have hb: inc (Q x *z Q (y *q z)) BZps by apply: ZpsS_prod. 
have hc: intp ((P x *z P y) *z P z) by apply:ZSp => //; apply:ZSp.
have hd:= (ZpsS_prod (ZpsS_prod qxp qyp) qzp).
apply /(BQ_of_pair_prop5 ha hb hc hd).
rewrite - (BZprodA  qx qy qz) - (BZprodA  px py pz).
set u := (P y *z P z); set v := (Q y *z Q z).
have uz: intp u by apply:ZSp.
have vz: intp v by apply:ZSp.
have he: intp (Q x *z v) by apply:ZSp.
have hf: intp (P x *z u) by apply:ZSp.
have hi: intp (P (y *q z) *z v) by apply:ZSp.
have hj: intp (Q (y *q z) *z u) by apply:ZSp.
rewrite - BZprodA // - BZprodA // (BZprodC (Q x)) (BZprodA pyz vz qx). 
rewrite (BZprodC (P x) u) (BZprodA qyz uz px) (BZprodC _ (Q x)) BZprodA //.
rewrite (BZprodC _ (P x)) (BZprodA qx px hj) (BZprodC (P x)).
apply: f_equal.
rewrite  /BQprod /BQ_of_pair  -lock /BQ_of_pair_internal pr1_pair pr2_pair -/u -/v.
move: (BZgcd_div uz vz); set p := BZgcd u v; move => [e1 e2].
rewrite {2} e1 {1} e2 (BZprodC p) (BZprodC p).
move:(BZgcd_s2 uz vz) => [pZ u'Z v'Z].
rewrite BZprodA // BZprodA // (BZprodC (u %/z p)) //.
Qed.


Lemma BQprod_AC x y z: ratp x -> ratp y -> ratp z ->
  (x *q y) *q z = (x *q z) *q y.
Proof.
move => xq yq zq.
by rewrite - (BQprodA xq yq zq) - (BQprodA xq zq yq) (BQprodC y).
Qed.


Lemma BQprod_CA x y z: ratp x -> ratp y -> ratp z ->
  x *q (y *q z) = y *q (x *q z).
Proof.
by move => xz yz zz;rewrite (BQprodA xz yz zz) (BQprodA yz xz zz) (BQprodC x y).
Qed.

Lemma BQprod_ACA a b c d: ratp a -> ratp b -> ratp c -> ratp d ->
    (a *q b) *q (c *q d) = (a *q c) *q (b *q d).
Proof.
move => az bz cz dz; move: (QSp cz dz) (QSp bz dz)=>  cdz bdz.
by rewrite -!BQprodA // (BQprod_CA bz cz dz).
Qed.

Lemma BQprodDr x y z: ratp x -> ratp y -> ratp z  ->
   x *q (y +q z) = (x *q y) +q (x *q z).
Proof. 
move => xq yq zq.
have H: forall x y, ratp x -> ratp y ->  
  Q (x *q y) *z (P x *z P y) = P (x *q y) *z (Q x *z Q y).
  clear; move => x y xq yq; rewrite /BQprod /BQ_of_pair  -lock /BQ_of_pair_internal.
  move /BQ_P: xq => [_ px /BZps_sBZ qx _].
  move /BQ_P: yq => [_ py /BZps_sBZ qy _].
  move:(BZgcd_div (ZSp px py) (ZSp qx qy)).
  move:(BZgcd_s2 (ZSp px py) (ZSp qx qy)).
  set a := (P x *z P y); set b:= (Q x *z Q y); set p := BZgcd a b.
  aw; move =>  [pZ u'Z v'Z] [e1 e2]; rewrite {2} e2  {1} e1.
  by rewrite BZprodC BZprodA // (BZprodC p).   
move: (QSs yq zq)  (QSp xq yq)  (QSp xq zq) => yzq xyq xzq.
move /BQ_P: (xq) => [_ px qxp _]; move:(BZps_sBZ qxp) => qx.
move /BQ_P: (yq) => [_ py qyp _]; move:(BZps_sBZ qyp) => qy.
move /BQ_P: (zq) => [_ pz qzp _]; move:(BZps_sBZ qzp) => qz.
move /BQ_P: yzq => [_ pyz qyzp _]; move:(BZps_sBZ qyzp) => qyz.
move /BQ_P: xyq => [_ pxy qxyp _]; move:(BZps_sBZ qxyp) => qxy.
move /BQ_P: xzq => [_ pxz qxzp _]; move:(BZps_sBZ qxzp) => qxz.
set N := P x *z (P y *z Q z +z Q y *z P z).
set D := Q x *z (Q y *z Q z).
have ha: intp (P x *z P (y +q z)) by apply:ZSp.
have hb: inc (Q x *z Q (y +q z)) BZps by apply:ZpsS_prod.
have hc: intp N by apply:ZSp => //; apply:ZSs => //; apply:ZSp.
have hd: inc D BZps by apply:(ZpsS_prod qxp (ZpsS_prod qyp qzp)).
have he:intp (P (x *q y) *z Q (x *q z) +z Q (x *q y) *z P (x *q z)).
  by apply:ZSs; apply:ZSp.
have hf: inc (Q (x *q y) *z Q (x *q z)) BZps by apply:ZpsS_prod.
transitivity (BQ_of_pair N D).
apply /(BQ_of_pair_prop5 ha hb hc hd).
  have ra: intp (Q y *z Q z)  by apply: ZSp.
  have rb: intp (P y *z Q z +z Q y *z P z) by apply:ZSs; apply:ZSp.
  rewrite BZprodC /D - BZprodA // - (@BZprodA (Q x)) //; congr (_ *z _).
  rewrite BZprodC - BZprodA // (BZprodC _ N) /N - BZprodA //;congr (_ *z _).
  rewrite /BQsum /BQ_of_pair  -lock /BQ_of_pair_internal pr1_pair pr2_pair.
  set N1 := (P y *z Q z +z Q y *z P z).
  move:(BZgcd_div rb ra)(BZgcd_s2 rb ra); move => [e1 e2][rc rd re].
  set p :=  BZgcd N1 (Q y *z Q z);rewrite /N1 {2} e1 {1} e2.
  by rewrite BZprodA // (BZprodC (N1 %/z p)).
apply /(BQ_of_pair_prop5 hc hd he hf).
set Pxy := (P x *z P y); set Pxz := (P x *z P z).
set Qxy := (Q x *z Q y); set Qxz := (Q x *z Q z).
have ra: intp (P y *z Q z) by apply:ZSp.
have rb: intp (Q y *z P z) by apply:ZSp.
have rc: intp D by apply:BZps_sBZ.
have rd: intp (P (x *q y) *z Q (x *q z)) by apply:ZSp.
have re: intp (Q (x *q y) *z P (x *q z)) by apply:ZSp.
have rf: intp (Q (x *q y) *z Q (x *q z)) by apply:ZSp.
have rg: intp Pxy by apply:ZSp.
have rh: intp Pxz by apply:ZSp.
have ri: intp (Pxy *z Q z) by apply: ZSp.
have rj: intp (Pxz *z Q y) by apply: ZSp.
have rk: intp Qxy by apply: ZSp.
have rl: intp (Q x *z Q z) by apply: ZSp.
have -> : N =  Pxy *z (Q z) +z Pxz *z (Q y).
  by rewrite /N  BZprodDr// - BZprodA// - BZprodA// (BZprodC (Q y) (P z)).
rewrite BZprodDr // BZprodC BZprodDr //; congr  (_ +z _).
  rewrite (BZprodC (Q (x *q y))) - BZprodA // (@BZprodA D) // BZprodC.
  have ->: D = (Qxy  *z Q z) by rewrite /D  BZprodA.
  rewrite BZprodA // (BZprodC ((Qxy *z Q z)))  BZprodA // H //.
rewrite  (BZprodC D) - (BZprodA) // - (BZprodA) //.
have ->: D =  (Q x *z Q z) *z Q y by rewrite /D (BZprodC (Q y)) - BZprodA //.
by rewrite  (BZprodA qxz rh qy) (H _ _ xq zq) - BZprodA //.
Qed.

Lemma BQprodDl x y z: ratp x -> ratp y -> ratp z  ->
   (y +q z) *q x = (y *q x) +q (z *q x).
Proof.
move => xq yq zq; rewrite (BQprodC)  (BQprodC y) (BQprodC z).
by apply:BQprodDr.
Qed.

Lemma BQprod_cZ x y: intp x -> intp y -> 
  BQ_of_Z x *q  BQ_of_Z y = BQ_of_Z (x *z y).
Proof.
move => xz yz; move: (ZSp xz yz) => xyz.
rewrite /BQ_of_Z /BQprod /BQ_of_pair  -lock /BQ_of_pair_internal; aw.
rewrite (BZprod_1l ZS1) (BZgcd_x1 xyz) ! BZquo_one //; apply:ZS1.
Qed.

Lemma BQprod_22: \2q *q \2q = \4q.
Proof. by rewrite  (BQprod_cZ ZS2 ZS2) BZprod_22. Qed.

Lemma BQprod_0r x: ratp x -> x  *q \0q = \0q.
Proof. 
move /BQ_P => [_ _ pa _]; move:(BZps_sBZ pa) => pb.
rewrite /BQprod /BQ_zero /BQ_of_Z pr1_pair pr2_pair BZprod_0r.  
by rewrite BZprod_1r //; apply: BQnum0_P1. 
Qed.

Lemma BQprod_0l x: ratp x ->  \0q *q x = \0q.
Proof. move => h; by rewrite BQprodC BQprod_0r. Qed.


Lemma BQprod_1l x: ratp x ->  \1q *q x = x.
Proof.
move => xq; rewrite /BQprod /BQ_of_pair /BQ_one /BQ_of_Z; aw.
move /BQ_P: (xq) => [_ pa /BZps_sBZ pb _].
by rewrite BZprod_1l //  BZprod_1l //; apply: BQ_pr2.
Qed.

Lemma BQprod_1r x: ratp x ->  x *q \1q  = x.
Proof. by move => pa; rewrite BQprodC; apply BQprod_1l. Qed.

Lemma BQprod_m1r x: ratp x ->  x *q \1mq = BQopp x.
Proof. 
move => xq; rewrite /BQprod /BQ_of_pair /BQ_mone /BQ_of_Z; aw.
move /BQ_P: (xq) => [_ pa /BZps_sBZ pc  _].
move: (BQ_pr2 (QSo xq)); rewrite /BQopp; aw.
rewrite BZprod_1r // BZprod_m1r //. 
Qed.

Lemma BQprod_m1l x: ratp x -> \1mq *q x  = BQopp x.
Proof. by move => pa; rewrite  BQprodC; apply: BQprod_m1r. Qed.

Lemma BQopp_prod_r x y: ratp x -> ratp y ->
  BQopp (x *q y) = x *q (BQopp y).
Proof.
move => xq yq.
by rewrite - (BQprod_m1r (QSp xq yq)) - (BQprodA xq yq QSm1) (BQprod_m1r yq).
Qed.

Lemma BQopp_prod_l x y: ratp x -> ratp y ->
  BQopp (x *q y) = (BQopp x) *q y.
Proof. by move => xq yq; rewrite BQprodC (BQopp_prod_r yq xq)  BQprodC. Qed.

Lemma BQprod_opp_comm x y: ratp x -> ratp y ->
  x *q  (BQopp y) =  (BQopp x) *q y.
Proof.  move => xq yq; rewrite - BQopp_prod_l // BQopp_prod_r //. Qed.

Lemma BQprod_opp_opp x y: ratp x -> ratp y ->
  (BQopp x) *q (BQopp y) = x  *q y.
Proof. by move => xq yp; rewrite (BQprod_opp_comm (QSo xq) yp) BQopp_K. Qed.


Lemma QpsS_prod a b: inc a BQps -> inc b BQps -> inc (a *q b) BQps.
Proof. 
move => /Zo_P [/BQ_P [_ _ pb _ ] pa] /Zo_P [/BQ_P [_ _ qb _ ] qa].
by apply: BQ_of_pair_spos; apply:ZpsS_prod.
Qed.

Lemma QmsuS_prod a b: inc a BQms -> inc b BQms -> inc (a *q b) BQps.
Proof. 
move => aq bq.
move: (QpsS_prod (BQopp_negative1 aq) (BQopp_negative1 bq)).
by rewrite BQprod_opp_opp //; apply:BQms_sBQ.
Qed.

Lemma QpmsS_prod a b: inc a BQps -> inc b BQms -> inc (a *q b) BQms.
Proof. 
move => aq bq.
have h := (BQopp_negative1 bq).
rewrite -(BQopp_K (BQms_sBQ bq)). 
rewrite - (BQopp_prod_r (BQps_sBQ aq) (BQps_sBQ h)).
apply: BQopp_positive1; apply:(QpsS_prod aq h).
Qed.

Lemma QpS_prod a b: inc a BQp -> inc b BQp -> inc (a *q b) BQp.
Proof.
move: QpS0  => h ap bp; move:(BQp_sBQ ap)(BQp_sBQ bp) => aq bq.
case: (equal_or_not a \0q) => e1; first by rewrite e1 BQprod_0l.
case: (equal_or_not b \0q) => e2; first by rewrite e2 BQprod_0r.
by apply:(BQps_sBQp); apply:QpsS_prod; apply/BQps_iP.
Qed.

Lemma QmuS_prod a b: inc a BQm -> inc b BQm -> inc (a *q b) BQp.
Proof. 
move => az bz.
move: (QpS_prod (BQopp_negative2 az) (BQopp_negative2 bz)).
by rewrite BQprod_opp_opp //; apply: BQm_sBQ.
Qed.


Lemma QpmS_prod a b: inc a BQp -> inc b BQm -> inc (a *q b) BQm.
Proof. 
move => aqp bqm.
have h := (BQopp_negative2 bqm).
rewrite -(BQopp_K (BQm_sBQ bqm)).
rewrite - (BQopp_prod_r (BQp_sBQ aqp) (BQp_sBQ h)).
apply: BQopp_positive2; apply:(QpS_prod aqp h).
Qed.

Lemma BQps_stable_prod1 a b: ratp a -> ratp b -> inc (a *q b) BQps ->
  ((inc a BQps <-> inc b BQps) /\ (inc a BQms <-> inc b BQms)).
Proof. 
move => aq bq.
move:BQ_di_neg_spos => H.
case /BQ_i1P: (aq) => pa; first by rewrite pa (BQprod_0l bq) => /BQps_iP [_].
  case /BQ_i1P: bq; first by move ->; rewrite (BQprod_0r aq)  => /BQps_iP [_].
    move => pb pc;split; split => // h; [case: (H _ h pa) | case:(H _ h pb)].
   move => pb pc;case: (H _ _ pc); exact: (QpmsS_prod pa pb).
case /BQ_i1P: bq; first by move ->; rewrite (BQprod_0r aq)  => /BQps_iP [_].
  move => pb pc; case: (H _ _ pc); rewrite BQprodC; exact (QpmsS_prod pb pa).
move => pb pc; split => //; split => h; [case: (H _ pa h) | case: (H _ pb h)].
Qed.


Lemma BQprod_abs x y: ratp x -> ratp y ->  
  BQabs (x *q y) = (BQabs x) *q (BQabs y).
Proof. 
move => xq yq.
case /BQ_i0P: (xq)=> pa; case /BQ_i0P: (yq)=> pb.
+ rewrite (BQabs_negs pa) (BQabs_negs pb) (BQprod_opp_opp xq yq).
  by rewrite (BQabs_pos (BQps_sBQp (QmsuS_prod pa pb))).
+ rewrite (BQabs_negs pa) (BQabs_pos pb) - ( BQopp_prod_l xq yq).
  by rewrite BQprodC (BQabs_neg (QpmS_prod pb (BQms_sBQm pa))).
+ rewrite (BQabs_negs pb) (BQabs_pos pa) - ( BQopp_prod_r xq yq).
  by rewrite  (BQabs_neg (QpmS_prod pa (BQms_sBQm pb))).
+ by rewrite (BQabs_pos pa) (BQabs_pos pb) (BQabs_pos (QpS_prod pa pb)).
Qed.

Lemma BQprod_nz x y: ratp x -> ratp y ->
  x <> \0q -> y <> \0q -> x *q y <> \0q.
Proof. 
move => xq yq xnz ynz.
move: (xq)(yq) => /BQ_P [_ xn xd _] /BQ_P [_ yn yd _].
move / (BQ_of_pair_zero (ZSp xn yn) (ZpsS_prod xd yd)).
apply:(BZprod_nz xn yn); [ by move/(BQnum0_P xq) | by move/(BQnum0_P yq)].
Qed.


Lemma BQprodBr x y z: ratp x -> ratp y -> ratp z  ->
   x *q (y -q z) = (x *q y) -q (x *q z).
Proof. 
move => xq yq qgt0x; rewrite /BQdiff (BQprodDr xq yq (QSo qgt0x)). 
by rewrite BQopp_prod_r. 
Qed.

Lemma BQprodBl x y z: ratp x -> ratp y -> ratp z  ->
  (y -q z) *q x =  (y *q x) -q  (z *q x).
Proof. 
by move => xq yq qgt0x; rewrite BQprodC (BQprodC y)  (BQprodC z) BQprodBr.
Qed.


Definition BQ_of_nat n := BQ_of_Z (BZ_of_nat n).

Lemma QpsS_of_nat n: natp n -> n <> \0c -> inc (BQ_of_nat n) BQps.
Proof. 
move => sa sn; apply:BQ_of_Z_iQps; apply/BZps_iP. 
split; [by apply:BZ_of_natp_i | by move/pr1_def].
Qed.

Lemma QpS_of_nat n: natp n -> inc (BQ_of_nat n) BQp.
Proof. by  move => / BZ_of_natp_i /BQ_of_Z_iQp. Qed.

Lemma QS_of_nat n: natp n -> inc (BQ_of_nat n) BQ.
Proof. by move => /QpS_of_nat /BQp_sBQ. Qed.

Lemma  BQpsS_fromN1 n: natp n -> inc (BZ_of_nat (csucc n))  BZps.
Proof.
move => nN; apply /BZps_iP; split. 
   by apply:BZ_of_natp_i;apply:NS_succ.
move/BZ_of_nat_inj; apply: succ_nz.
Qed.

Lemma BQpsS_fromN n: natp n -> inc (BQ_of_nat (csucc n)) BQps.
Proof. by move => nN;apply:BQ_of_Z_iQps; apply:BQpsS_fromN1.  Qed.


Lemma BQsum_cN n m: natp n -> natp m ->
  BQ_of_nat n +q  BQ_of_nat m = BQ_of_nat (n +c m).
Proof.
move => sa sb; rewrite /BQ_of_nat - (BZsum_cN sa sb). 
by apply:BQsum_cZ;apply:BZ_of_nat_i.
Qed.

Lemma BQ_of_nat_succ n: natp n ->  BQ_of_nat n +q \1q =  BQ_of_nat (csucc n).
Proof. by move => nN; rewrite (BQsum_cN nN NS1) (Nsucc_rw nN). Qed.

Lemma qle_cN a b: natp a -> natp b ->
    (a <=c b <-> BQ_of_nat a <=q BQ_of_nat b).
Proof.
move => az bz.
by apply: (iff_trans (zle_cN az bz)); apply:qle_cZ; apply:BZ_of_nat_i.
Qed.

Lemma qlt_cN a b: natp a -> natp b ->
    (a <c b <-> BQ_of_nat a <q BQ_of_nat b).
Proof.
move => aN bN.
by apply: (iff_trans (zlt_cN aN bN)); apply:qlt_cZ; apply:BZ_of_nat_i.
Qed.

Lemma BQ_of_nat_injective: injective  BQ_of_nat. 
Proof. by move => n m /= /pr1_def /pr1_def. Qed.

Definition BQsquare x := x *q x.

Lemma BQpS_square x: ratp x -> inc (BQsquare x) BQp.
Proof.
case/BQ_i0P => h; first exact:(BQps_sBQp(QmsuS_prod h h)).
exact: (QpS_prod h h).
Qed.

Lemma BQ_squarep x: ratp x -> 
   BQsquare x = J (Qnum x *z Qnum x) (Qden x *z Qden x).
Proof.
move => xq; move /BQ_P:(xq) => [_ nz dzp cp]; move: (BZps_sBZ dzp)=> dz.
rewrite /BQsquare /BQprod /BQ_of_pair  -lock /BQ_of_pair_internal.
set p := BZgcd (P x *z P x) (Q x *z Q x).
suff: p = \1z by move ->; rewrite ! BZquo_one //; apply:ZSp.
have ha: BZcoprime (Q x) (P x)  by rewrite /BZcoprime BZgcd_C.
have hb: BZcoprime (P x *z P x) (Q x).    
  by rewrite /BZcoprime BZgcd_C  BZgcd_simp. 
by rewrite /p BZgcd_simp //;  apply:ZSp.
Qed.

Lemma BQ_square_Z x y: ratp x -> BQsquare x = BQ_of_Z y -> 
   [/\ inc y BZp, Qnum x *z Qnum x = y & Qden x = \1z].
Proof.
move => xq; rewrite (BQ_squarep xq) => sqx.
move /BQ_P: xq => [_ nz dzp _]; move:(BZps_sBZ dzp) => dz.
have pe: inc (P x *z P x) BZp.
  case /BZ_i0P: nz => ha; first exact:(BZps_sBZp (ZmsuS_prod ha ha)).
  exact:(ZpS_prod ha ha).
move:(pr1_def sqx) => sa;split => //; first by ue. 
move:(pr2_def sqx) => /(BZprod_1_inversion_l dz dz) [_] [] // xn.
rewrite xn in dzp; case: (BZ_di_neg_spos ZmsS_m1 dzp).
Qed.

Lemma BQ_square_1 x: ratp x -> 
   (BQsquare x = \1q <-> (x = \1q \/ x = \1mq) ).
Proof.
move => xq; split.
  move /BQ_P:(xq) => [pa nz _ _ ].
  move /(BQ_square_Z xq) => [_ /(BZprod_1_inversion_l nz nz) [_ sa] sb].
  by case: sa => sa; [left | right]; rewrite - pa sa sb.
case => ->; rewrite /BQsquare.
  by rewrite (BQprod_1l QS1).
by rewrite (BQprod_m1l QSm1) BQopp_m1.
Qed.

Lemma BQ_square_2 x : ratp x -> BQsquare x = \2q -> False.
Proof.
move => xq; move /(BQ_square_Z xq) => [_  eq1 _].
move: eq1; rewrite BZprodE /BZprod_int; Ytac0; move /pr1_def.
move /BQ_P:xq => [_ /BZ_valN nn _ _ ].
case: (equal_or_not (P (P x)) \0c) => qa;first by rewrite qa cprod0l;fprops.
case: (equal_or_not (P (P x)) \1c) => qb;first by rewrite qb cprod1l;fprops.
move:(cge2 (CS_nat nn) qa qb) clt_24  => qc lt1 eq1.
by move: (cprod_Mlele qc qc); rewrite eq1 cprod_22 => /(cltNge lt1).
Qed.

Lemma BQ_nat_square_monotone n (x := BQ_of_nat n) : natp n  -> 
  x <=q BQsquare x.
Proof.
move => nN.
have nz:= (BZ_of_nat_i nN).
have nzp := (BZ_of_natp_i nN).
rewrite /BQ_of_nat/BQsquare (BQprod_cZ nz nz).
apply/ (qle_cZ nz (ZSp nz nz)).
rewrite (BZprod_cN nN nN); apply/(zle_cN nN (NS_prod nN nN)).
case: (equal_or_not n \0c) => enz; first by rewrite enz; apply:cle0x; fprops.
exact:(cprod_M1le (CS_nat nN) enz).
Qed.


Lemma BQprod_cN a b: natp a -> natp b ->
  BQ_of_nat (a *c b) =  BQ_of_nat a *q (BQ_of_nat b).
Proof.
move => aN bN; rewrite /BQ_of_nat.
by rewrite (BQprod_cZ (BZ_of_nat_i aN) (BZ_of_nat_i bN)) (BZprod_cN aN bN).
Qed.

Definition BQdouble x := \2q *q x.

Lemma BQdouble_p x : ratp x -> x +q x = BQdouble x.
Proof. 
move => xq.
rewrite - {1 2} (BQprod_1l xq) /BQdouble - BQsum_11 (BQprodDl) //; apply:QS1.
Qed.

Lemma QSdouble x : ratp x -> inc (BQdouble x) BQ.
Proof. move => h; apply: (QSp QS2 h). Qed.


Lemma BQsum_square a b: ratp a -> ratp b ->
   BQsquare (a +q b) = BQsquare a +q BQsquare b +q BQdouble (a *q b). 
Proof.
move => aq bq.
move:(QSp aq aq)(QSp bq bq)(QSp aq bq)(QSs aq bq) => aaq bbq abq sabq.
rewrite {1}/BQsquare (BQprodDl sabq aq bq).
rewrite (BQprodDr aq aq bq) (BQprodDr bq aq bq) (BQprodC b a). 
rewrite (BQsumC (a *q b)) (BQsum_ACA aaq abq bbq abq).
by rewrite (BQdouble_p abq) BQprodC.
Qed.

Lemma BQdiff_square a b: ratp a -> ratp b ->
   BQsquare (a -q b) = BQsquare a +q BQsquare b -q (BQdouble (a *q b)). 
Proof.
move => aq bq.
rewrite (BQsum_square aq (QSo bq)).
rewrite {2}/BQsquare (BQprod_opp_opp bq bq).
by rewrite /BQdouble - (BQopp_prod_r aq bq) - (BQopp_prod_r QS2 (QSp aq bq)).
Qed.


Lemma BQsumdiff_square a b: ratp a -> ratp b ->
   BQsquare (a +q b) = \4q *q (a *q b) +q BQsquare (a -q b). 
Proof.
move => aq bq.
rewrite (BQdiff_square aq bq) (BQsum_square aq bq) - BQprod_22.
have ha := (QSp aq bq).
move: (BQdouble_p (QSdouble ha)); rewrite /BQdouble =>  hb.
rewrite - (BQprodA QS2 QS2 ha) - hb.
set u := (BQsquare a +q BQsquare b); set v := (BQdouble (a *q b)).
have uq: inc u BQ by apply:QSs;apply:QSp.
have vq: inc v BQ by apply:QSdouble; apply:QSp.
rewrite  (BQsum_ACA vq vq uq (QSo vq)) (BQsum_opp_r vq).
rewrite BQsumC (BQsum_0r (QSs vq uq)). rewrite /v /BQdouble.
done.
Qed.

Lemma BQdouble_opp x: ratp x -> BQdouble (BQopp x) = BQopp (BQdouble x).
Proof. move => xq;symmetry;exact:(BQopp_prod_r QS2 xq). Qed.

Lemma BQdoubleD x y: ratp x -> ratp y ->
   BQdouble (x +q y) = (BQdouble x) +q (BQdouble y).
Proof. apply: (BQprodDr QS2). Qed.

(** ** Inverse *)


Definition BQinv x :=
  Yo (inc (Qnum x) BZps) (J (Qden x) (Qnum x))
    (Yo (Qnum x = \0z) \0q (J (BZopp (Qden x)) (BZopp (Qnum x)))).

Lemma BQinv_0: BQinv \0q = \0q.
Proof.  
rewrite /BQinv /BQ_zero /BQ_of_Z; aw;Ytac0; rewrite Y_false//.
by move/BZps_iP => [_].
Qed.

Lemma BQinv_pos x: inc x BQps -> BQinv x = (J (Qden x) (Qnum x)).
Proof.  by move/Zo_P => [xQ px]; rewrite /BQinv (Y_true px). Qed.

Lemma BQinv_neg x: inc x BQms -> 
   BQinv x = J (BZopp (Qden x)) (BZopp (Qnum x)).
Proof. 
move/Zo_P => [xQ /BZms_iP [px py]]. 
rewrite /BQinv;Ytac0; Ytac h => //; case: (BZ_di_pos_neg h px).
Qed.

Lemma BQinv_opp x: ratp x -> BQinv (BQopp x) = BQopp (BQinv x).
Proof.
move => xq; move/BQ_P: (xq) => [_ nz dzp _]; move:(BZps_sBZ dzp)=> dz.
case /BQ_i1P: xq => xs.
+ by rewrite xs BQopp_0 BQinv_0 BQopp_0.
+ have h := (BQopp_positive1 xs).
  by rewrite (BQinv_pos xs) (BQinv_neg h) /BQopp !pr1_pair BZopp_K;aw.
+ have h := (BQopp_negative1 xs).
  by rewrite (BQinv_pos h) (BQinv_neg xs) /BQopp; aw; rewrite BZopp_K.
Qed.

Lemma QpsS_inv x: inc x BQps -> inc (BQinv x) BQps.
Proof.
move => xp; rewrite (BQinv_pos xp).
move/Zo_P: xp => [/BQ_P [_ nz dzp cp] nzp];move:(BZps_sBZ dzp)=> dz.
suff: (BQ_of_pair (Q x) (P x)) = (J (Q x) (P x)). 
  by move <-; apply: BQ_of_pair_spos.
by rewrite /BQ_of_pair  -lock /BQ_of_pair_internal BZgcd_C cp ! BZquo_one.
Qed.

Lemma QmsS_inv x: inc x BQms -> inc (BQinv x) BQms.
Proof.
move => xqm; move: (BQms_sBQ xqm) => xq.
move: (BQopp_negative1 xqm) => /QpsS_inv.
have [ha hb]: pairp (BQinv x) /\ intp (P (BQinv x)).
  rewrite (BQinv_neg xqm); split; fprops; aw.
  by move /BQ_P: xq => [_ _ /BZps_sBZ /ZSo dz _].
rewrite (BQinv_opp xq) => /BQopp_positive1.
by rewrite /BQopp pr1_pair pr2_pair BZopp_K // ha.
Qed.

Lemma QS_inv x: ratp x -> ratp (BQinv x).
Proof.
case /BQ_i1P => xs.
+ rewrite xs BQinv_0; apply: QS0.
+ by move: (QpsS_inv xs) => /BQps_sBQ.
+ by move: (QmsS_inv xs) => /BQms_sBQ.
Qed.


Lemma BQinv_K x: ratp x -> BQinv (BQinv x)  = x.
Proof.
move => xq; move/BQ_P: (xq) => [px nz /BZps_sBZ dz _].
case /BQ_i1P:xq => xs.
+ by rewrite xs BQinv_0 BQinv_0. 
+ move: (QpsS_inv xs) => ixs.
  by rewrite (BQinv_pos ixs) (BQinv_pos xs); aw.
+ move: (QmsS_inv xs) => ixs.
  rewrite (BQinv_neg ixs) (BQinv_neg xs); aw.
  by rewrite (BZopp_K nz) (BZopp_K dz).
Qed.

Lemma BQinv_inj x y: ratp x -> ratp y -> BQinv x = BQinv y -> x = y.
Proof. by move => /BQinv_K e1 /BQinv_K e2 e3; rewrite - e1 - e2 e3. Qed.

Lemma BQinv_Z x: inc x BZps -> BQinv (BQ_of_Z x) = BQ_of_Zinv x.
Proof.
by move => xp; rewrite (BQinv_pos (BQ_of_Z_iQps xp)) /BQ_of_Z; aw.
Qed.

Lemma BQinv_1: BQinv \1q = \1q. 
Proof. exact: (BQinv_Z ZpsS1). Qed.

Lemma BQinv_m1: BQinv \1mq = \1mq. 
Proof. by rewrite - BQopp_1 (BQinv_opp QS1) BQinv_1. Qed.

Lemma BQinv_2: BQinv \2q = \2hq. 
Proof. exact: (BQinv_Z ZpsS2). Qed.

Lemma BQinv_abs x: ratp x -> BQabs (BQinv x) = BQinv (BQabs x).
Proof. 
move => xq.
case/BQ_i1P: (xq) => h.
+ by rewrite h BQabs_0 BQinv_0 BQabs_0.
+ by rewrite (BQabs_pos (BQps_sBQp(QpsS_inv h))) (BQabs_pos (BQps_sBQp h)).
+ by rewrite (BQabs_negs (QmsS_inv h)) (BQabs_negs h) (BQinv_opp xq).
Qed.

Lemma BQprod_inv1 x : ratp x -> x <> \0q -> (x *q  (BQinv x)) = \1q.
Proof. 
wlog xp:x /(inc x BQps).
  move => H xq xns; case /BQ_i1P:xq => xs //. 
    by apply:(H _ xs (BQps_sBQ xs) xns).
  move: (BQopp_negative1 xs) => oxp. 
  move:(BQms_sBQ xs) => xq; move:(QSo xq)=> oxq.
  rewrite -( BQprod_opp_opp xq (QS_inv xq)) - (BQinv_opp xq); apply: H => //.
  by move /BQps_iP:oxp => [_ ].
move => _ _ ;rewrite (BQinv_pos xp) /BQprod; aw.
move/Zo_P: xp => [/BQ_P [_ sa sb _] sc].
move: (ZpsS_prod sb sc)=> /BZps_iP [hb hd]; move:(BZp_sBZ hb) => hc.
rewrite BZprodC /BQ_of_pair  -lock /BQ_of_pair_internal (BZgcd_id hc) (BZabs_pos hb).
by rewrite(proj2(BZdvd_itself hc hd)).
Qed.


Lemma BQ_inv_prop a b: ratp a -> ratp b -> a *q b = \1q -> b = BQinv a.
Proof.
move => aq bq h.
have ha: ratp (BQinv a) by apply:QS_inv.
case: (equal_or_not a \0q) => az.
  by move: h; rewrite az BQprod_0l // => hh; case:BQ1_nz.
move: (f_equal (fun z => (BQinv a) *q z) h). 
rewrite BQprodA // BQprod_1r // (BQprodC _ a) (BQprod_inv1) // BQprod_1l //.
Qed.


Lemma BQprod_inv x y:ratp x -> ratp y ->
   BQinv (x *q y) = BQinv x *q BQinv y.
Proof.
move => pa pb.
have pc :=QS_inv pa.
have pd :=QS_inv pb.
case: (equal_or_not x \0q) => xz.
   rewrite xz BQinv_0 BQprod_0l // BQinv_0 BQprod_0l //.
case: (equal_or_not y \0q) => yz.
   rewrite yz BQinv_0 BQprod_0r // BQinv_0 BQprod_0r //.
symmetry; apply:BQ_inv_prop; try apply:QSp => //.
rewrite BQprod_ACA // !BQprod_inv1 // BQprod_1l //; apply: QS1.
Qed.


Definition BQdiv x y := x *q  (BQinv y).

Notation "x /q y" := (BQdiv x y) (at level 40).

Lemma QS_div x y: ratp x -> ratp y -> ratp (x /q y).
Proof. by move => xq /QS_inv yq; apply:QSp. Qed.

Lemma BQdiv_0x x : ratp x -> \0q /q x = \0q.
Proof. by move => /QS_inv xq; apply: BQprod_0l. Qed.

Lemma BQdiv_x0 x : ratp x -> x /q \0q = \0q.
Proof. by move => xq; rewrite /BQdiv BQinv_0 BQprod_0r.  Qed.

Lemma BQdiv_1x x : ratp x -> \1q /q x = BQinv x.
Proof. by move => /QS_inv xq; apply: BQprod_1l. Qed.

Lemma BQdiv_x1 x : ratp x -> x /q \1q = x.
Proof. by move => xq; rewrite /BQdiv BQinv_1 BQprod_1r. Qed.


Lemma QpsS_div a b: inc a BQps -> inc b BQps -> inc (a /q b) BQps.
Proof.
move => ap bp; apply:QpsS_prod => //; apply: (QpsS_inv bp).
Qed.

Lemma QmsuS_div a b: inc a BQms -> inc b BQms -> inc (a /q b) BQps.
Proof.
move => ap bp; apply:QmsuS_prod => //; apply: (QmsS_inv bp).
Qed.


Lemma QpmsS_div a b: inc a BQps -> inc b BQms -> inc (a /q b) BQms.
Proof.
move => ap bp; apply:QpmsS_prod => //; apply: (QmsS_inv bp).
Qed.

Lemma QmpsS_div a b: inc a BQms -> inc b BQps -> inc (a /q b) BQms.
Proof.
move => ap bp; rewrite /BQdiv BQprodC.
apply:QpmsS_prod => //; apply: (QpsS_inv bp).
Qed.

Lemma QpS_div a b: inc a BQp -> inc b BQp -> inc (a /q b) BQp.
Proof.
move: QpS0 => izp ap bp; move:(BQp_sBQ ap)(BQp_sBQ bp)=> aq bq.
case: (equal_or_not a \0q) => az; first by rewrite az BQdiv_0x.
case: (equal_or_not b \0q) => bz; first by rewrite bz BQdiv_x0.
by apply/(BQps_sBQp); apply:QpsS_div; apply/BQps_iP.
Qed.

Lemma QmuS_div a b: inc a BQm -> inc b BQm -> inc (a /q b) BQp.
Proof.
move: QpS0 => izp ap bp; move:(BQm_sBQ ap)(BQm_sBQ bp)=> aq bq.
case: (equal_or_not a \0q) => az; first by rewrite az BQdiv_0x.
case: (equal_or_not b \0q) => bz; first by rewrite bz BQdiv_x0.
by apply/(BQps_sBQp); apply:QmsuS_div; apply/BQms_iP.
Qed.

Lemma BQpmS_div a b: inc a BQp -> inc b BQm -> inc (a /q b) BQm.
Proof.
move: QmS0 => izp ap bp;move:(BQp_sBQ ap)(BQm_sBQ bp)=> aq bq.
case: (equal_or_not a \0q) => az; first by rewrite az BQdiv_0x.
case: (equal_or_not b \0q) => bz; first by rewrite bz BQdiv_x0.
by apply/(BQms_sBQm); apply:QpmsS_div; [apply/BQps_iP | apply/BQms_iP ].
Qed.


Lemma BQmpS_div a b: inc a BQm -> inc b BQp -> inc (a /q b) BQm.
Proof.
move: QmS0 => izp ap bp; move:(BQm_sBQ ap)(BQp_sBQ bp)=> aq bq.
case: (equal_or_not a \0q) => az; first by rewrite az BQdiv_0x.
case: (equal_or_not b \0q) => bz; first by rewrite bz BQdiv_x0.
by apply/(BQms_sBQm); apply:QmpsS_div; [ apply/BQms_iP | apply/BQps_iP ].
Qed.

Lemma BQopp_div_r x y: ratp x -> ratp y ->
  BQopp (x /q y) = x /q (BQopp y).
Proof. 
by move => xq yq; rewrite /BQdiv (BQinv_opp yq) BQopp_prod_r //; apply:QS_inv.
Qed.

Lemma BQopp_div_l x y: ratp x -> ratp y ->
  BQopp (x /q y) = (BQopp x) /q y.
Proof. 
by move => xq yq; rewrite /BQdiv BQopp_prod_l //; apply:QS_inv.
Qed.

Lemma BQdiv_opp_comm x y: ratp x -> ratp y ->
  x /q  (BQopp y) =  (BQopp x) /q y.
Proof. by move => xq yq; rewrite - BQopp_div_l // BQopp_div_r. Qed.

Lemma BQdiv_opp_opp x y: ratp x -> ratp y ->
  (BQopp x) /q (BQopp y) = x /q y.
Proof. 
move => xq yq.
by rewrite -(BQopp_div_l xq (QSo yq)) -BQopp_div_r // BQopp_K //; apply: QS_div.
Qed.


Lemma BQdiv_abs x y: ratp x -> ratp y ->
  (BQabs x) /q (BQabs y) = BQabs (x /q y).
Proof. 
move => xq yq.
by rewrite /BQdiv (BQprod_abs xq (QS_inv yq)) (BQinv_abs yq).
Qed.


Lemma BQdiv_numden x: ratp x -> 
  (BQ_of_Z (Qnum x)) /q (BQ_of_Z (Qden x)) = x.
Proof.
wlog xp: x/ inc x BQps.
  move => H; case /BQ_i1P => xs.
  + rewrite xs BQnum0 BQden0 -/BQ_zero -/BQ_one /BQdiv BQprod_0l ?BQinv_1 //.
    apply: QS1.
  + by apply: H => //; apply: BQps_sBQ.
  + move:(BQopp_negative1 xs) => h; move: (BQps_sBQ h) => h1.
    move: (BQms_sBQ xs) => xq.
    move/BQ_P: (xq) => [_ pa /BZps_sBZ pb _]; move:(ZSo pa) => pc.
    move: (H _ h h1); rewrite {1 2} /BQopp; aw => sa.
    move: (f_equal BQopp sa); rewrite (BQopp_K xq) => {3} <-.
    rewrite BQopp_div_l; try apply /BQ_of_Z_iQ => //;congr (_ /q _).
    by rewrite /BQ_of_Z /BQopp pr1_pair BZopp_K //; aw.
move => xq; move/BQ_P: (xq) => [_ pb pc _].
have pf := BZps_sBZ pc. 
rewrite /BQdiv (BQinv_pos (BQ_of_Z_iQps pc)) /BQ_of_Z /BQprod; aw. 
by rewrite BZprod_1r //  BZprod_1l // BQ_pr2.
Qed.

Lemma BQdiv_numden1 a b (q := BQ_of_Z a /q  BQ_of_Z b):
   intp a -> inc b BZps -> BZcoprime a b ->
  (Qnum q = a /\ Qden q = b).
Proof.
move => az bz abc.
suff: q = J a b by  move => ->; aw. 
rewrite / q /BQdiv /BQinv /BQ_of_Z pr1_pair (Y_true bz) /BQprod; aw.
rewrite (BZprod_1r az)  (BZprod_1l (BZps_sBZ bz)) /BQ_of_pair  -lock /BQ_of_pair_internal abc.
by rewrite (BZquo_one az) (BZquo_one (BZps_sBZ bz)).
Qed.

Lemma BQdiv_xx x : ratp x -> x <> \0q -> (x /q x) = \1q.
Proof. apply:BQprod_inv1. Qed.

Lemma BQ_self_inv x: ratp x ->
   (x = BQinv x <-> [\/ x= \0q, x = \1q | x = \1mq]).
Proof.
move => xq; split.
   move => h; case: (equal_or_not x \0q) => e0; first by constructor 1. 
   move: (f_equal (fun z => x *q z) h).
   rewrite (BQprod_inv1 xq e0) => /(BQ_square_1 xq).
   by case => hh;[constructor 2 | constructor 3].
by case => ->; [rewrite BQinv_0 | rewrite BQinv_1 | rewrite BQinv_m1 ].
Qed.


Lemma BQdiv_square a b: ratp a -> ratp b -> 
    BQsquare (a /q b) = (BQsquare a) /q (BQsquare b).
Proof.
move => aq bq; rewrite /BQsquare /BQdiv.
move: (QS_inv bq) => ibq.
rewrite (BQprod_ACA aq ibq aq ibq).
by rewrite (BQprod_inv bq bq).
Qed.



Section BQdiffProps3.
Variables (x y z: Set).
Hypotheses (xq: ratp x)(yq: ratp y)(zq: ratp z).

Lemma BQdiv_sumDl: 
   (y +q z) /q x = (y /q x) +q (z /q x).
Proof. by rewrite /BQdiv BQprodDl //; apply: QS_inv. Qed.

Lemma BQdiv_prod_simpl_l: x <> \0q ->  (x *q y) /q  (x *q z) = y /q z.
Proof.
move => xnz.
rewrite /BQdiv (BQprod_inv xq zq) (BQprodC x y).
rewrite (BQprodA (QSp yq xq) (QS_inv xq) (QS_inv zq)).
by rewrite  -(BQprodA yq xq (QS_inv xq))  BQprod_inv1 // BQprod_1r.
Qed.

Lemma BQdiv_prod_comm: (x *q y) /q z = (x /q z) *q y.
Proof. 
by rewrite /BQdiv (BQprodC x y) (BQprodC _ y) -(BQprodA yq xq) //; apply:QS_inv.
Qed.


Lemma BQinv_div: BQinv (x /q y) = y /q x.
Proof.
rewrite /BQdiv (BQprod_inv xq (QS_inv yq)). 
by rewrite (BQinv_K yq) BQprodC.
Qed.

Lemma BQdiv_prod: x <> \0q -> (x *q y) /q x = y.
Proof. 
move => h; rewrite /BQdiv BQprodC (BQprodA (QS_inv xq) xq yq).
by rewrite (BQprodC _ x)  BQprod_inv1 // BQprod_1l.
Qed.

Lemma BQprod_div: x <> \0q -> x *q (y /q x) = y.
Proof. 
move => h.
rewrite /BQdiv (BQprodC y) (BQprodA xq (QS_inv xq) yq).  
by rewrite BQprod_inv1 // BQprod_1l.
Qed.

End BQdiffProps3.

Section BQdiffProps4.
Variables (x y z: Set).
Hypotheses (xq: ratp x)(yq: ratp y)(zq: ratp z).

Lemma BQprod_div_ea: y <> \0q -> x = y *q z -> z = x /q y.
Proof. by move => h -> ; rewrite BQdiv_prod. Qed.

Lemma BQdiv_diag_rw:  x /q y = \1q -> x = y.
Proof. 
move => h. 
case: (equal_or_not y \0q) => h'.
   by move: h; rewrite h' (BQdiv_x0 xq) => hh; case BQ1_nz.
move:(f_equal (BQprod y) h); rewrite (BQprod_div yq xq h').
by rewrite BQprod_1r.
Qed.

Lemma BQdiv_prod_simpl_r:  z <> \0q -> (x *q z) /q (y *q z) = x /q y.
Proof.  
by move => h; rewrite (BQprodC x z) (BQprodC y z);  apply: BQdiv_prod_simpl_l.
Qed.

Lemma BQprod_eq2r: z <> \0q ->  x *q z = y *q z -> x = y.
Proof.
move => qgt0x h; rewrite - (BQdiv_prod zq xq qgt0x) - (BQdiv_prod zq yq qgt0x).
by rewrite BQprodC h BQprodC.
Qed.

Lemma BQprod_eq2l:  x <> \0q -> x *q y = x *q z -> y = z.
Proof.
move => qgt0x h; rewrite - (BQdiv_prod xq yq qgt0x).
by rewrite - (BQdiv_prod xq zq qgt0x) h.
Qed.

End  BQdiffProps4.

Lemma BQdiv_div_simp a b c: ratp a -> ratp b -> ratp c -> b <> \0q ->
    (a /q b) /q (c /q b) = a /qc.
Proof.
move => aq bq cq bnz. 
move:  (QS_inv bq)  (QS_inv cq) => biq ciq.
rewrite /BQdiv (BQinv_div cq bq) (BQprodC a).
rewrite (BQprod_ACA biq aq bq ciq) (BQprodC  _ b) BQprod_inv1 //.
by rewrite BQprod_1l //; apply:QSp.
Qed.

Lemma BQdiv_div2 a b c:
   ratp a -> ratp b -> ratp c -> a /q (b *q c) = (a /q b) /q c.
Proof.
move => aq bq cq.
by rewrite /BQdiv (BQprod_inv bq cq) BQprodA //; apply: QS_inv.
Qed.

Lemma BQsum_div a b c: ratp a -> ratp b -> ratp c -> c <> \0q ->
   a +q (b /q c) = (a *q c +q b) /q c.
Proof.
move => aq bq cq cnz; move:(QS_inv cq) => icq.
have {1} -> : a = (a *q c) /q c by rewrite BQprodC BQdiv_prod //.
by rewrite - BQprodDl //; apply: QSp.
Qed.

Lemma BQdiff_div a b c: ratp a -> ratp b -> ratp c -> c <> \0q ->
   a -q (b /q c) = (a *q c -q b) /q c.
Proof.
move => aq bq cq cnz; move:(QSo bq) => obq.
by rewrite /BQdiff (BQopp_div_l bq cq);  apply: BQsum_div.
Qed.



(** ** The sign function *)

Definition BQsign x:= BZsign (Qnum x).
Definition BQQsign x := BQ_of_Z (BQsign x).

Lemma QS_sign x: intp (BQsign x).
Proof. exact:ZS_sign. Qed.

Lemma QS_qsign x: ratp (BQQsign x).
Proof.  apply: BQ_of_Z_iQ;  exact:ZS_sign. Qed.

Lemma BQsign_trichotomy a:  BQsign a = \1z \/ BQsign a = \1mz \/ BQsign a = \0z.
Proof.  exact: BZsign_trichotomy. Qed.

Lemma BQsign_pos x: inc x BQps -> BQsign x = \1z.
Proof. by move /Zo_hi; apply:BZsign_pos. Qed.

Lemma BQsign_neg x: inc x BQms -> BQsign x = \1mz.
Proof. by move /Zo_hi; apply:BZsign_neg. Qed.

Lemma BQsign_0: BQsign \0q = \0z.
Proof. by  rewrite /BQsign BQnum0; exact: BZsign_0. Qed.

Lemma BQ_sign_prop x: ratp x -> 
   [/\ inc x BQps <-> BQsign x = \1z,
       inc x BQms <-> BQsign x = \1mz &
       x = \0q <->  BQsign x = \0z].
Proof.
move => xq.
move: BZ1_nz BZm1_nz => n1 n2.
have n3:(\1mz <> \1z). 
  move:C1_ne_C0 => h.
  by rewrite  /BZ_mone /BZm_of_nat (Y_false h) => /pr2_def /nesym.
move:(@BQsign_pos x) (@BQsign_neg x) (BQsign_0) => pa pb pc.
split; split => // h; case/BQ_i1P:xq => // xv.
+ by move: h; rewrite xv pc // => w; case n1.
+ by move: (pb xv); rewrite h => h1; case: n3.
+ by move:h; rewrite xv pc => h; case n2.
+ by move: (pa xv); rewrite h. 
+ by rewrite h.
+ by rewrite h.
+ by rewrite h.
+ by move:(pa xv); rewrite h => w; case n1.
+ by move:(pb xv); rewrite h => w; case n2.
Qed.

Lemma BQopp_sign x: ratp x -> (BQsign (BQopp x)) = BZopp (BQsign x).
Proof.
by move/BQ_P => [_ xq _ _]; rewrite /BQopp /BQsign pr1_pair BZopp_sign //.
Qed.


Lemma BQinv_sign x: ratp x -> BQsign (BQinv x) = BQsign x.
Proof.
case/BQ_i1P => xs. 
+ by rewrite xs BQinv_0. 
+ by rewrite (BQsign_pos (QpsS_inv xs)) (BQsign_pos xs).
+ by rewrite (BQsign_neg (QmsS_inv xs)) (BQsign_neg xs).
Qed.


Lemma BQprod_sign x y: ratp x -> ratp y ->  
  BQsign (x *q y) = (BQsign x) *z (BQsign y).
Proof. 
move => xq yq.
wlog h: x xq / inc x BQps.
  move => H; case/BQ_i1P:(xq) => xz.
  + by rewrite xz (BQprod_0l yq) ! BQsign_0 BZprod_0l.
  + by apply: H.
  + move:(H _ (QSo xq) (BQopp_negative1 xz)).
    have pa: intp (BQsign (x *q y)) by apply:ZS_sign.
    have pb: intp (BQsign x) by apply:ZS_sign.
    have pc: intp (BQsign y) by apply:ZS_sign.
    rewrite - (BQopp_prod_l xq yq) (BQopp_sign (QSp xq yq)) (BQopp_sign xq).
    by rewrite -  BZopp_prod_l //; apply: BZopp_inj => //;apply: ZSp.
move:ZS1 ZSm1=> z1 zz1;case/BQ_i1P:(yq) => yz.
+  by rewrite yz (BQprod_0r xq) ! BQsign_0 BZprod_0r. 
+  by rewrite ! BQsign_pos //; [ rewrite BZprod_1l | apply:QpsS_prod].
+ rewrite (BQsign_pos h) (BQsign_neg yz) BZprod_1l //.
  by rewrite (BQsign_neg) //; apply:QpmsS_prod.
Qed.

Lemma BQdiv_sign x y: ratp x -> ratp y ->  
  BQsign (x /q y) = (BQsign x) *z (BQsign y).
Proof. 
by move => xq yq; rewrite /BQdiv (BQprod_sign xq (QS_inv yq)) (BQinv_sign yq).
Qed.

Lemma BQabs_sign x: ratp x -> x = (BQQsign x) *q (BQabs x).
Proof.
move => xq; case /BQ_i1P: (xq) => xs. 
+ rewrite xs BQabs_0 BQprod_0r //; apply:QS_qsign.
+ by rewrite (BQabs_pos (BQps_sBQp xs)) /BQQsign (BQsign_pos xs) BQprod_1l.
+ rewrite (BQabs_negs xs)  /BQQsign  (BQsign_neg xs) (BQprod_m1l (QSo xq)).
  by rewrite (BQopp_K xq).
Qed.

Lemma BQsign_abs x: ratp x -> x *q (BQQsign x) = BQabs x.
Proof. 
move => xq; case /BQ_i1P: (xq) => xs.
+ rewrite xs BQabs_0 BQprod_0l //; apply:QS_qsign.
+ by rewrite (BQabs_pos (BQps_sBQp xs)) /BQQsign (BQsign_pos xs) BQprod_1r.
+ by rewrite (BQabs_negs xs)  /BQQsign  (BQsign_neg xs) (BQprod_m1r xq). 
Qed.


Lemma BQabs_diff a b: ratp a -> ratp b ->
   BQabs (a -q b)= BQabs (b -q a).
Proof. by move => aq bq; rewrite - (BQoppB bq aq) BQabs_opp. Qed.


Lemma qle_diffP a b: ratp a -> ratp b ->  (a <=q b <-> inc (b -q a) BQp).
Proof. 
move => aq bq. 
move /BQ_P: (aq) => [_ pa pb _]; move: (BZps_sBZ pb) => pc.
move /BQ_P: (bq) => [_ qa qb _]; move: (BZps_sBZ qb) => qc.
rewrite /BQdiff /BQsum /BQopp pr1_pair pr2_pair.
set x := (P b *z Q a +z Q b *z BZopp (P a)).
have aux: P a *z Q b <=z Q a *z P b <-> inc x BZp.
  rewrite /x (BZprodC (P b)) -(BZopp_prod_r qc pa) (BZprodC (Q b)).
  exact: (zle_diffP (ZSp pa qc) (ZSp pc qa)).
move: (ZpsS_prod qb pb) => dp.
split; first by move => [_ _ /aux h]; apply:(BQ_of_pair_pos h dp).
move => h; split => //; apply/aux.
have: intp x by apply:ZSs; apply:ZSp => //; apply: ZSo.
case/BZ_i0P => // h2. 
by case:(BQ_di_neg_pos(BQ_of_pair_sneg h2 (ZpsS_prod qb pb)) h).
Qed.

Lemma qle_diffP1 a b: ratp a -> ratp b -> 
  (a <=q b <-> \0q <=q  (b -q a)).
Proof. 
move => pa pb; apply: (iff_trans (qle_diffP pa pb)).
symmetry; apply:qle0xP. 
Qed.

Lemma qlt_diffP a b: ratp a -> ratp b -> 
  (a <q b <-> inc (b -q a) BQps).
Proof.
move => pa pb; split.
  move => [] /(qle_diffP pa pb) => pc pd; apply /BQps_iP;split => //.
  dneg aux; symmetry; exact (BQdiff_xx_rw pb pa aux).
move /BQps_iP => []  /(qle_diffP pa pb) pc pd; split => //.
by dneg aux; rewrite aux (BQdiff_xx pb).
Qed.

Lemma qlt_diffP1 a b: ratp a -> ratp b -> 
  (\0q  <q (b -q a) <-> a <q b).
Proof. 
move => pa pb; apply: iff_sym; apply: (iff_trans (qlt_diffP pa pb)).
apply:iff_sym ;exact:qlt0xP.
Qed.

Lemma qlt_diffP2 a b: ratp a -> ratp b -> 
  (a <q b <-> inc (a -q b) BQms).
Proof. 
move => pa pb; apply: (iff_trans (qlt_diffP pa pb)).
rewrite - (BQoppB pb pa); split => h.
  by apply: BQopp_positive1.
rewrite - (BQopp_K (QS_diff pb pa)); apply: (BQopp_negative1 h).
Qed.


Lemma qlt_diffP3 a b c: ratp a -> ratp b -> ratp c ->
  (a <q b -q c <->  a +q c <q b).
Proof.
move => aq bq cq.
move: (qlt_diffP1 (QSs aq cq) bq).
rewrite BQsumC (BQdiff_diff2 bq cq aq).
apply: (iff_trans (iff_sym (qlt_diffP1 aq (QS_diff bq cq)))).
Qed.


Lemma qlt_diffP4 a b c: ratp a -> ratp b -> ratp c -> 
  (b -q c <q a <-> b <q a +q c).
Proof.
move => aq bq cq.
move:(qlt_diffP1 (QS_diff bq cq) aq).
rewrite(BQdiff_diff aq bq cq) (BQsum_AC aq (QSo bq) cq) => ha.
exact: (iff_trans (iff_sym ha) (qlt_diffP1 bq (QSs aq cq))).
Qed.

Lemma qgt_diffP  a b: ratp a -> ratp b -> (a -q b <q \0q <-> a <q b).
Proof.
move => aq bq;  rewrite - (BQoppB bq aq).
apply:iff_sym;apply: (iff_trans(qlt_diffP aq bq)); split.
  by move => /BQopp_positive1 / qgt0xP.
by move/ qgt0xP => /BQopp_negative1; rewrite BQopp_K //; apply:QS_diff.
Qed.

Lemma BQsum_le2l a b c: ratp a -> ratp b -> ratp c -> 
  ((c +q a) <=q (c +q b) <-> a <=q b).
Proof. 
move => pa pb pc.
apply: (iff_trans (qle_diffP (QSs pc pa) (QSs pc pb))).
apply: iff_sym;apply: (iff_trans (qle_diffP pa pb)).
by rewrite BQdiff_sum_simpl_l.
Qed.

Lemma BQsum_le2r a b c: ratp a -> ratp b -> ratp c ->
  ((a +q c) <=q (b +q c) <-> a <=q b).
Proof. 
rewrite (BQsumC a c) (BQsumC b c); apply: BQsum_le2l. 
Qed.

Lemma BQsum_lt2l a b c: ratp a -> ratp b -> ratp c -> 
  (c +q a <q c +q b <-> a <q b).
Proof.
move => pa pb pc.
apply: (iff_trans (qlt_diffP (QSs pc pa) (QSs pc pb))).
apply: iff_sym;apply: (iff_trans (qlt_diffP pa pb)).
by rewrite BQdiff_sum_simpl_l.
Qed.

Lemma BQsum_lt2r a b c: ratp a -> ratp b -> ratp c ->
  (a +q c <q b +q c <-> a <q b).
Proof. 
rewrite (BQsumC a c) (BQsumC b c); apply: BQsum_lt2l. 
Qed.


Lemma BQdiff_lt1P a b c: ratp a -> ratp b -> ratp c ->
  (a -q b <q c <-> a -q c <q  b).
Proof.
move => aq bq cq.
move: (BQsum_lt2r (QS_diff aq bq) cq bq).
rewrite (BQsum_diff1 bq aq) => ha.
move: (BQsum_lt2r (QS_diff aq cq) bq cq).
rewrite (BQsum_diff1 cq aq) BQsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.

Lemma BQdiff_le1P a b c: ratp a -> ratp b -> ratp c ->
  (a -q b <=q c <-> a -q c <=q  b).
Proof.
move => aq bq cq.
move: (BQsum_le2r (QS_diff aq bq) cq bq).
rewrite (BQsum_diff1 bq aq) => ha.
move: (BQsum_le2r (QS_diff aq cq) bq cq).
rewrite (BQsum_diff1 cq aq) BQsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.


Lemma BQdiff_lt2P a b c: ratp a -> ratp b -> ratp c ->
  (c <q a -q b <-> b <q a -q c).
Proof.
move => aq bq cq.
move: (BQsum_lt2r cq (QS_diff aq bq) bq).
rewrite (BQsum_diff1 bq aq) => ha.
move: (BQsum_lt2r bq (QS_diff aq cq) cq).
rewrite (BQsum_diff1 cq aq) BQsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.

Lemma BQdiff_le2P a b c: ratp a -> ratp b -> ratp c ->
  (c <=q a -q b <-> b <=q a -q c).
Proof.
move => aq bq cq.
move: (BQsum_le2r cq (QS_diff aq bq) bq).
rewrite (BQsum_diff1 bq aq) => ha.
move: (BQsum_le2r bq (QS_diff aq cq) cq).
rewrite (BQsum_diff1 cq aq) BQsumC => hb.
exact: (iff_trans (iff_sym ha) hb).
Qed.


Lemma BQabs_prop3 x y e: ratp x -> ratp y -> ratp e ->
  (BQabs (x -q y) <=q e <->  y -q e <=q x /\ x <=q y +q e).
Proof.
move => xr yr er.
have Ha: BQopp e <=q x -q y <-> y -q e <=q x.
  rewrite - (BQoppB yr xr).
  exact (iff_trans (qle_oppP (QS_diff yr xr) er) (BQdiff_le1P yr xr er)).
have Hb: x -q y <=q e <->  x <=q y +q e.
  move:(BQsum_le2r xr (QSs yr er) (QSo yr)). 
  by rewrite -/(_ -q _)  -/(_ -q _)  (BQdiff_sum yr er).
move:(BQabs_prop1 (QS_diff xr yr) er) => H.
split; first by move/H => [/Ha ha /Hb hb].
by move => [/Ha ha /Hb hb]; apply/H.
Qed.

Lemma BQabs_prop4 x y e: ratp x -> ratp y -> ratp e ->
  (BQabs (x -q y) <q e <->  y -q e <q x /\ x <q y +q e).
Proof.
move => xr yr er.
have Ha: BQopp e <q x -q y <-> y -q e <q x.
  rewrite - (BQoppB yr xr).
  exact (iff_trans (qlt_oppP (QS_diff yr xr) er) (BQdiff_lt1P yr xr er)).
have Hb: x -q y <q e <->  x <q y +q e.
  move:(BQsum_lt2r xr (QSs yr er) (QSo yr)). 
  by rewrite -/(_ -q _)  -/(_ -q _)  (BQdiff_sum yr er).
move:(BQabs_prop2 (QS_diff xr yr) er) => H.
split; first by move/H => [/Ha ha /Hb hb].
by move => [/Ha ha /Hb hb]; apply/H.
Qed.

Lemma BQsum_Mlele a b c d: a <=q c ->  b <=q d -> (a +q b) <=q (c +q d).
Proof.
move => eq1 eq2; move: (proj32 eq1)  (proj31 eq2)=> cz bz.
move /(BQsum_le2r (proj31 eq1) cz bz): eq1 => eq3.
move/(BQsum_le2l bz (proj32 eq2) cz): eq2 => eq4.
BQo_tac.
Qed.

Lemma BQsum_Mlelt a b c d: a <=q c -> b <q d -> (a +q b) <q (c +q d).
Proof.
move => eq1 eq2; move: (proj32 eq1)  (proj31_1 eq2)=> cz bz.
move /(BQsum_le2r (proj31 eq1) cz bz): eq1 => eq3.
move/(BQsum_lt2l bz (proj32_1 eq2) cz): eq2 => eq4.
BQo_tac.
Qed.

Lemma BQsum_Mltle a b c d: a <q c -> b <=q d -> (a +q b) <q (c +q d).
Proof.
by move => eq1 eq2; rewrite (BQsumC a)(BQsumC c); apply:BQsum_Mlelt.
Qed.

Lemma BQsum_Mltlt a b c d: a <q c -> b <q d -> (a +q b) <q (c +q d).
Proof. by move => eq1 [eq2 _]; apply: BQsum_Mltle. Qed.


Lemma BQsum_Mlege0 a c d: a <=q c ->  \0q <=q d -> a <=q (c +q d).
Proof.
by move => pa pb; move: (BQsum_Mlele pa pb);rewrite (BQsum_0r  (proj31 pa)).
Qed.

Lemma BQsum_Mlegt0 a c d: a <=q c ->  \0q <q d -> a <q (c +q d).
Proof.
by move => pa pb; move: (BQsum_Mlelt pa pb); rewrite (BQsum_0r  (proj31 pa)).
Qed.

Lemma BQsum_Mltge0 a c d: a <q c ->  \0q <=q d -> a <q (c +q d).
Proof.
by move => pa pb; move: (BQsum_Mltle pa pb); rewrite (BQsum_0r (proj31_1 pa)).
Qed.

Lemma BQsum_Mltgt0 a c d: a <q c ->  \0q <q d -> a <q (c +q d).
Proof.
by move => pa pb; move: (BQsum_Mltlt pa pb);rewrite (BQsum_0r (proj31_1 pa)).
Qed.

Lemma BQsum_Mlele0 a b c : a <=q c ->  b <=q \0q -> (a +q b) <=q c.
Proof. 
by move => pa pb; move: (BQsum_Mlele pa pb); rewrite (BQsum_0r (proj32 pa)).
Qed.

Lemma BQsum_Mlelt0 a b c : a <=q c ->  b <q \0q -> (a +q b) <q c.
Proof. 
by move => pa pb; move: (BQsum_Mlelt pa pb); rewrite (BQsum_0r (proj32 pa)).
Qed.

Lemma BQsum_Mltle0 a b c : a <q c ->  b <=q \0q -> (a +q b) <q c.
Proof. 
by move => pa pb; move: (BQsum_Mltle pa pb); rewrite (BQsum_0r (proj32_1 pa)).
Qed.
 
Lemma BQsum_Mltlt0 a b c : a <q c ->  b <q \0q -> (a +q b) <q c.
Proof. 
by move => pa pb; move: (BQsum_Mltlt pa pb);  rewrite (BQsum_0r (proj32_1 pa)).
Qed.

Lemma BQsum_Mp a b: ratp a -> inc b BQp ->  a <=q (a +q b).
Proof. 
move => pa pb.
move/ qle0xP: pb => eq1; exact:(BQsum_Mlege0 (qleR pa) eq1).
Qed.

Lemma BQsum_Mps a b: ratp a -> inc b BQps ->  a <q (a +q b).
Proof. 
move => pa pb.
move / qlt0xP: pb => eq1; exact:(BQsum_Mlegt0 (qleR pa) eq1).
Qed.

Lemma BQsum_Mm a b: ratp a -> inc b BQm ->  (a +q b) <=q a.
Proof. 
move => pa pb.
by move  / qge0xP: pb => eq1; move:(BQsum_Mlele0 (qleR pa) eq1).
Qed.

Lemma BQsum_Mms a b: ratp a -> inc b BQms ->  (a +q b) <q a.
Proof. 
move => pa pb.
by move / qgt0xP: pb => eq1; move:(BQsum_Mlelt0 (qleR pa) eq1).
Qed.

Lemma qlt_succ x: ratp x -> x <q x +q \1q.
Proof. move => h; exact:(BQsum_Mps h QpsS1). Qed.


Lemma BQprod_Mlege0 a b c: inc c BQp -> a <=q b -> (a *q c)  <=q (b *q c).
Proof. 
move => cp ab; move: (ab) => [az bz _]; move: (BQp_sBQ cp) => cz.
move /(qle_diffP az bz): ab => p1.
apply/ (qle_diffP (QSp az cz) (QSp bz cz)). 
by rewrite - BQprodBl //;apply:QpS_prod.
Qed.

Lemma BQprod_Mltgt0 a b c: inc c BQps -> a <q b -> (a *q c) <q (b *q c).
Proof. 
move => cp ab; move: (ab) => [[az bz _]_]; move: (BQps_sBQ cp) => cz.
move /(qlt_diffP az bz): ab => p1.
apply/(qlt_diffP (QSp az cz) (QSp bz cz)).
by rewrite - BQprodBl //;apply:QpsS_prod.
Qed.

Lemma BQprod_Mlele0 a b c: inc c BQm -> a <=q b -> (b *q c)  <=q (a *q c).
Proof. 
move => cm; move: (BQopp_negative2 cm) => ocp ineq. 
move:  (BQprod_Mlege0 ocp (qle_opp ineq)).
move: ineq => [az bz _]; move: (BQm_sBQ cm) => cz.
rewrite BQprod_opp_opp // BQprod_opp_opp //.
Qed.

Lemma BQprod_Mltlt0 a b c: inc c BQms -> a <q b -> (b *q c) <q (a *q c).
Proof. 
move => cm; move: (BQopp_negative1 cm) => ocp ineq. 
move:  (BQprod_Mltgt0 ocp (qlt_opp ineq)).
move: ineq => [[az bz _] _]; move: (BQms_sBQ cm) => cz.
rewrite BQprod_opp_opp // BQprod_opp_opp //.
Qed.

Lemma BQprod_Mpp  b c: inc b BQp -> \1q <=q c -> b <=q (b *q c).
Proof.
move => pa pb.
by rewrite BQprodC - {1} (BQprod_1l (BQp_sBQ pa)); apply: BQprod_Mlege0.
Qed.

Lemma BQprod_Mpp1 a b: \1q <=q a -> \1q <=q b -> \1q <=q a *q b.
Proof.
move => a1 b1.
have [h _]: \0q <q \1q by move / qlt0xP:QpsS1.
have ap: inc a BQp by apply / qle0xP; BQo_tac.
exact:(qleT a1 (BQprod_Mpp ap b1)).
Qed.

Lemma BQprod_Mlepp a b c: inc b BQp -> \1q <=q c -> a <=q b -> a <=q (b *q c).
Proof. 
move => pa pb pc; move: (BQprod_Mpp pa pb) => pd; BQo_tac.
Qed.

Lemma BQprod_Mltpp a b c: inc b BQp -> \1q <=q c  -> a <q b -> a <q (b *q c).
Proof. 
move => pa pb pc; move: (BQprod_Mpp  pa pb) => pd;  BQo_tac.
Qed.

Lemma BQprod_Mlelege0 a b c d: inc b BQp -> inc c BQp ->
  a <=q b -> c <=q  d -> (a *q c)  <=q (b *q d).
Proof. 
move => pa pb pc pd.
move: (BQprod_Mlege0 pb pc) (BQprod_Mlege0 pa pd) => r1.
rewrite  (BQprodC c) (BQprodC d) => r2; BQo_tac.
Qed.

Lemma BQprod_Mltltgt0 a b c d: inc b BQps -> inc c BQps ->
  a <q b -> c <q  d -> (a *q c)  <q (b *q d).
Proof. 
move => pa pb pc pd.
move: (BQprod_Mltgt0 pb pc) (BQprod_Mltgt0 pa pd) => r1.
rewrite  (BQprodC c) (BQprodC d) => r2; BQo_tac.
Qed.

Lemma BQprod_Mltltge0 a b c d: inc a BQp -> inc c BQp ->
  a <q b -> c <q  d -> (a *q c)  <q (b *q d).
Proof. 
move => pa pb pc pd.
have H: (forall a b, inc a BQp ->  a <q b -> inc b BQps).
  move => u v up uv; move: (uv) => [[uz vz _] _].
  move/ (qlt_diffP uz vz): uv => pe; move: (QpsS_sum_r up pe).
  by rewrite BQsum_diff.
move: (H _ _ pa pc) (H _ _ pb pd) => bp cp.
case: (equal_or_not c \0q) => cnz.
  rewrite cnz BQprod_0r; [ by apply / qlt0xP;  apply: QpsS_prod | BQo_tac ].
by apply: BQprod_Mltltgt0 => //; apply/ BQps_iP;split.
Qed.

Lemma BQprod_ple2r a b c: ratp a -> ratp b -> inc c BQps ->
  ((a *q c)  <=q (b *q c) <-> a <=q b).
Proof.
move => pa pb pc; split; last by apply:BQprod_Mlege0;apply:BQps_sBQp.
move => h; case: (qleT_el pa pb) => // h1.
move: (BQprod_Mltgt0 pc h1) => h2; BQo_tac.
Qed.

Lemma BQprod_plt2r a b c: ratp a -> ratp b ->  inc c BQps ->
  ((a *q c)  <q (b *q c) <-> a <q b).
Proof.
move => pa pb pc; split; last by apply:BQprod_Mltgt0. 
move => h; case: (qleT_el pb pa) => //.
move /(BQprod_ple2r pb pa pc) => h2; BQo_tac.
Qed.


Lemma BQprod_mle2r a b c: ratp a -> ratp b -> inc c BQms ->
  ((b *q c)  <=q (a *q c) <-> a <=q b).
Proof.
move => pa pb pc; split; last by apply:BQprod_Mlele0;apply:BQms_sBQm.
move => h; case: (qleT_el pa pb) => // h1.
move: (BQprod_Mltlt0 pc h1) => h2; BQo_tac.
Qed.

Lemma BQprod_mlt2r a b c: ratp a -> ratp b ->  inc c BQms ->
  ((b *q c)  <q (a *q c) <-> a <q b).
Proof.
move => pa pb pc; split; last by apply:BQprod_Mltlt0.
move => h; case: (qleT_el pb pa) => //.
move /(BQprod_mle2r pb pa pc) => h2; BQo_tac.
Qed.

Lemma BQprod_Mlt1 a b: ratp a -> inc b BQps ->
    (a /q b <q \1q <-> a<q b).
Proof.
move =>ap bp;  move:(QpsS_inv bp) => cp.
move/ BQps_iP: bp => [/BQp_sBQ bq bnz].
by move: (BQprod_plt2r ap bq cp); rewrite (BQprod_inv1 bq bnz).
Qed.


Lemma BQdiv_Mlelege0 a b c d: 
   ratp a -> inc b BQps -> ratp c -> inc d BQps ->
   ( a /q b <=q c /q d <-> a *q d <=q b *q c).
Proof.
move => aq bqps cq dqps.
move/ BQps_iP: (bqps) => [/BQp_sBQ bq bnz].
move/ BQps_iP: (dqps) => [/BQp_sBQ dq dnz].
have idq :=QS_inv dq.
have pb:=QSp cq bq.  
have pa:=QSp pb idq. 
move:(BQprod_ple2r (QS_div aq bq) (QS_div cq dq) bqps).
rewrite BQprodC (BQprod_div bq aq bnz) BQprodC (BQprodA bq cq idq) (BQprodC b).
move:(BQprod_ple2r aq  pa dqps).
rewrite  -/(_ /q d) (BQprodC ((c *q b) /q d)) (BQprod_div dq pb dnz).
move => sa sb; exact:(iff_sym(iff_trans sa sb)).
Qed.


Lemma BQdiv_Mltltge0 a b c d: 
   ratp a -> inc b BQps -> ratp c -> inc d BQps ->
   ( a /q b <q c /q d <-> a *q d <q b *q c).
Proof.
move => aq bqps cq dqps.
move/ BQps_iP: (dqps) => [/BQp_sBQ dq dnz].
move/ BQps_iP: (bqps) => [/BQp_sBQ bq bnz].
have qq: ratp (BQinv d) by apply: QS_inv.
split; move => [sa sb];split. 
+ by apply/(BQdiv_Mlelege0 aq bqps cq dqps).
+ dneg h; move: (f_equal (fun z => z /q d) h).
  rewrite BQprodC (BQdiv_prod dq aq dnz) => h1.
  rewrite (f_equal (fun z => z /q b) h1).
  by rewrite {2} /BQdiv - BQprodA // BQdiv_prod //; apply:QSp.
+ by apply/(BQdiv_Mlelege0 aq bqps cq dqps).
+ dneg h; move: (f_equal (fun z => z *q b) h).
  rewrite BQprodC BQprod_div // => ->.
  rewrite /BQdiv (BQprodC c)- (BQprodA qq cq bq) (BQprodC (BQinv d)).
by rewrite BQprodC ( BQprodC b); apply: BQprod_div => //; apply:QSp.
Qed.


Lemma BQinv_mon a b: inc a BQps -> inc b BQps  ->
   (\1q /q a <=q \1q /q b <-> b <=q a).
Proof.
move => pa pb; move:(BQps_sBQ pa)(BQps_sBQ pb)=> pa' pb'.
by move: (BQdiv_Mlelege0 QS1 pa QS1 pb); rewrite BQprod_1l //  BQprod_1r //.
Qed.

Lemma BQinv_mon1 a b: inc a BQps -> inc b BQps  ->
   (BQinv a <=q BQinv b <-> b <=q a).
Proof.
move => pa pb.
rewrite - (BQdiv_1x (BQps_sBQ pa)) - (BQdiv_1x (BQps_sBQ pb)).
apply: (BQinv_mon pa pb).
Qed.

Lemma BQinv_mon2 a b: inc a BQps -> inc b BQps  ->
   (BQinv a <q BQinv b <-> b <q a).
Proof.
move => pa pb; split; move => [ha hb]; split.
+ by apply /BQinv_mon1.
+ by dneg h; rewrite h.
+ by apply /BQinv_mon1.
+ by move /(BQinv_inj  (BQps_sBQ pa) (BQps_sBQ pb)) => /nesym.
Qed.

Lemma BQdiv_lt1P  a b c:   ratp a -> inc b BQps -> inc c BQps ->
    (a /q b <q c <-> a /q c <q b).
Proof.
move => aq bp cp. 
move/BQps_iP: (bp) => [/BQp_sBQ bq bnz].
move/BQps_iP: (cp) => [/BQp_sBQ cq cnz].
move: (BQprod_plt2r (QS_div aq bq) cq bp).
rewrite BQprodC (BQprod_div bq aq bnz) => h1.
move: (BQprod_plt2r (QS_div aq cq) bq cp).
rewrite BQprodC (BQprod_div cq aq cnz)  BQprodC => h2.
exact: (iff_trans (iff_sym h1) h2).
Qed.

Lemma BQdiv_le1P a b c: ratp a -> inc b BQps -> inc c BQps ->
  (a /q b <=q c <-> a /q c <=q  b).
Proof.
move => aq bp cp. 
move/BQps_iP: (bp) => [/BQp_sBQ bq bnz].
move/BQps_iP: (cp) => [/BQp_sBQ cq cnz].
move: (BQprod_ple2r (QS_div aq bq) cq bp).
rewrite BQprodC (BQprod_div bq aq bnz) => h1.
move: (BQprod_ple2r (QS_div aq cq) bq cp).
rewrite BQprodC (BQprod_div cq aq cnz)  BQprodC => h2.
exact: (iff_trans (iff_sym h1) h2).
Qed.

Lemma BQdiv_Mle1 a b c: ratp a -> ratp b -> inc c BQps ->
     ( a <=q b *q c <->  a /q c <=q b).
Proof.
move => aq bq cqp; move:(QpsS_inv cqp) => ip.
move/BQps_iP: (cqp) => [/BQp_sBQ cp cnz].
split => h.  
  move:  (BQprod_Mlege0 (BQps_sBQp ip) h).
  rewrite (BQprodC b) -! /(BQdiv _ _)  BQdiv_prod //.
move:  (BQprod_Mlege0 (BQps_sBQp cqp) h).
rewrite BQprodC  BQprod_div //.
Qed.


Lemma Qdiv_Mlelege1 a c d: ratp a ->  ratp c -> inc d BQps ->
   (a <=q c /q d <-> a *q d <=q c).
Proof.
move => pa pc pd.
move:(BQdiv_Mlelege0 pa QpsS1 pc pd).
by rewrite (BQprod_1l pc) (BQdiv_x1 pa).
Qed.

Lemma Qdiv_Mltltge1 a c d: ratp a -> ratp c -> inc d BQps ->
   (a <q c /q d <-> a *q d <q c).
Proof.
move => pa pc pd.
move:(BQdiv_Mltltge0 pa QpsS1 pc pd).
by rewrite (BQprod_1l pc) (BQdiv_x1 pa).
Qed.


Lemma Qdiv_Mltltge2 a b c: ratp a ->  inc b BQps -> ratp c ->
   (a /q b  <q c <-> a <q b *q c).
Proof.
move => pa pb pc.
move:(BQdiv_Mltltge0 pa pb pc QpsS1).
by rewrite (BQprod_1r pa) (BQdiv_x1 pc).
Qed.

Lemma qle_abs x: ratp x -> x <=q (BQabs x).
Proof. 
move => xq;case /BQ_i0P: (xq) => xp.
  move: (QpSa xq) => / qle0xP pa; move / qgt0xP: xp => [pb _]; BQo_tac.
by rewrite (BQabs_pos xp); apply:qleR.
Qed.

Lemma qle_triangular n m: ratp n -> ratp m -> 
  (BQabs (n +q m)) <=q (BQabs n) +q (BQabs m).
Proof.
move: n m.
pose aux n m := BQabs (n +q m) <=q BQabs n +q BQabs m.
suff: forall n m, inc n BQp -> ratp m -> aux  n m.
  move => h n m; case /BQ_i0P; last by apply: h.
  move => pa pb; rewrite - (BQabs_opp) - (BQabs_opp n)- (BQabs_opp m).
  rewrite (BQoppD (BQms_sBQ pa) pb); apply: h (QSo pb).
  apply:(BQopp_negative2 (BQms_sBQm pa)).
move => n m np; case  /BQ_i0P; last first.
  move => mp; rewrite /aux (BQabs_pos np) (BQabs_pos mp).
  move:(QpS_sum np mp) => pa; move: (BQp_sBQ pa) => pb.
  rewrite (BQabs_pos pa); apply: (qleR pb).
move => mn; rewrite /aux.
move: (BQp_sBQ np) (BQms_sBQ mn) => nq mq.
have pa : \0q <=q BQabs n +q BQabs m.
  by apply / qle0xP; apply: (QpS_sum);apply: QpSa.
case /BQ_i1P: (QSs nq mq) => sa.
+ by rewrite sa BQabs_0.
+ rewrite (BQabs_pos (BQps_sBQp sa)). 
 move: (qle_abs mq); rewrite (BQabs_pos np).
 by move /(BQsum_le2l mq (QSa mq) nq).
+ rewrite (BQabs_negs sa) (BQabs_pos np)  (BQabs_negs mn).
  rewrite (BQoppD nq mq). 
  apply/(@BQsum_le2r (BQopp n) n (BQopp m) (QSo nq) nq (QSo mq)).
  move / qge0xP: (BQopp_positive2 np) => sb.
  move/ qle0xP: np => sc; BQo_tac.
Qed.



(** The floor function *)

Definition BQfloor x := (Qnum x) %/z (Qden x).

Lemma ZS_floor x: ratp x -> intp (BQfloor x).
Proof.
by move => /BQ_P [_ pa /BZps_sBZ pb _];apply:ZS_quo.
Qed.


Lemma QpS_floor x: inc x BQp -> inc (BQfloor x) BZp.
Proof.
by move => /Zo_P[ /BQ_P [_ pa /BZps_sBZp pb _] pc]; apply: ZpS_quo.
Qed.

Lemma BQ_floor_aux x: intp x  ->
   (BQ_of_Z x) +q \1q = BQ_of_Z (x +z \1z). 
Proof.   move => xz; rewrite BQsum_cZ //; apply: ZS1. Qed.


Lemma BQ_floorp x (y := (BQ_of_Z (BQfloor x))) : ratp x -> 
    (y <=q x /\ x <q y +q \1q).
Proof.
move => xq; move: (xq) => /BQ_P [_ pa pb _]. 
move/ BZps_iP: (pb) => [/ BZp_sBZ bz bnz]. 
move: (BZdvd_correct pa bz bnz); rewrite -/(BQfloor x).
set r := (P x %%z Q x); move => [sa sb [sc sd _]].
rewrite (BZabs_pos  (BZps_sBZp pb)) in sd.
have re:  intp r by apply: ZS_rem.
have sf: intp (Q x *z BQfloor x) by apply: ZSp.
have yQ: ratp y by apply:BQ_of_Z_iQ; apply:  ZS_floor.
have rbb: inc (BQ_of_Z (Q x)) BQps by  by apply: BQ_of_Z_iQps.
have ra: ratp (BQ_of_Z r) by apply: BQ_of_Z_iQ.
have rb: ratp (BQ_of_Z (Q x)) by apply: BQ_of_Z_iQ.
have rc: BQ_of_Z (Q x) <> \0q by move/pr1_def.
move: (BQsum_div yQ ra rb rc). 
rewrite {2} /y BQprodC (BQprod_cZ bz sa) (BQsum_cZ sf re) - sc.
rewrite (BQdiv_numden xq) => <-; split.
  by apply:BQsum_Mp=> //;apply: QpS_div; apply:BQ_of_Z_iQp =>//;apply:BZps_sBZp.
have rd: ratp (BQ_of_Z r /q BQ_of_Z (Q x)) by apply: QS_div.
apply / (BQsum_lt2l rd QS1 yQ); apply /(BQprod_Mlt1 ra rbb).
apply/ qlt_cZ => //.
Qed.

Lemma BQ_floorp2 x z (y := (BQ_of_Z z)) : ratp x -> intp z ->
    (y <=q x /\ x <q y +q \1q) -> z = BQfloor x.
Proof.
move => xq zz [pa pb]; move:(BQ_floorp xq) => [pc pd].
have pe: inc (BQfloor x) BZ by apply:ZS_floor.
have pf: intp (z +z \1z) by apply:(ZSs zz ZS1).
have pg:intp (BQfloor x +z \1z) by apply:ZSs ZS1. 
rewrite (BQ_floor_aux pe) in pd; rewrite (BQ_floor_aux zz) in pb.
move /(qlt_cZ pe pf):  (qle_ltT pc pb) => /(zlt_succ1P pe zz) l1.
move /(qlt_cZ zz pg): (qle_ltT pa pd) =>  /(zlt_succ1P zz pe) l2.
BZo_tac.
Qed.

Lemma BQ_floorp3 x: ratp x -> exists2 y, inc y BZ & x <q (BQ_of_Z y).
Proof.
move => xq; move: (ZS_floor xq) => yz; move: (BQ_floorp xq) => [_].
rewrite (BQsum_cZ yz ZS1) => h.
exists (BQfloor x +z \1z) => //; apply:(ZSs yz ZS1).
Qed.

Lemma BQ_floorp4 x: ratp x -> exists2 y, inc y Nat & x <q (BQ_of_nat y).
Proof.
move /BQ_floorp3 => [m mz le1].
case/BZ_i0P: (mz) => h.
   move/zgt0xP: h => [/(qle_cZ mz ZS0)] => ha.
   exists \0c;[ apply:NS0 | BQo_tac].
exists (BZ_val m); first by apply: BZ_valN.
by rewrite/BQ_of_nat (BZp_hi_pr h).
Qed.

Lemma BQpsS_fromN_large e: inc e BQps -> 
    exists2 n, natp n &  BQinv  (BQ_of_nat (csucc n)) <q e.
Proof.
move => ep.
move:(QpsS_inv ep) => ies.
move: (BQ_floorp4 (BQps_sBQ ies)) => [n na nb].
have nc:(BQ_of_nat n <q BQ_of_nat (csucc n)).
  by move/(qlt_cN na (NS_succ na)): (cltS na).
move:(qlt_ltT nb nc) => h.
move/(BQinv_mon2 (BQpsS_fromN na) ies):h; rewrite (BQinv_K (BQps_sBQ ep)) => h.
by exists n.
Qed.


Lemma BQfloor_M x y: x <=q y -> BQfloor x <=z BQfloor y.
Proof.
move => h; move:(h) => [xq yq _].
move: ( BQ_floorp xq)( BQ_floorp yq) => [sa _][_ sd].
move: (ZS_floor xq) => fxz.
move: (ZS_floor yq) => fyz.
move: (qle_ltT (qleT sa h)  sd); rewrite (BQsum_cZ fyz ZS1).
by move / (qlt_cZ fxz (ZSs fyz ZS1)) => /(zlt_succ1P fxz fyz).
Qed.

Lemma BQfloor_Z x: intp x -> BQfloor (BQ_of_Z x) = x.
Proof.
by move => xz; rewrite /BQfloor /BQ_of_Z pr1_pair pr2_pair BZquo_one. 
Qed.

Lemma BQfloor_0: BQfloor \0q = \0z.
Proof. apply: (BQfloor_Z ZS0). Qed.


Lemma BQ_floor_zero a b: inc a BQp -> a <q b -> BQfloor (a/q b) = \0z.
Proof.
move => ap cab.
have aq := (BQp_sBQ ap). 
have bqps: inc b BQps by apply/ qlt0xP; apply: qle_ltT cab; apply/ qle0xP.
have pa: inc (a /q b) BQp by  apply:(QpS_div ap (BQps_sBQp bqps)).
have pb: BQ_of_Z \0z <=q a /q b by apply / qle0xP.
have pc: a /q b <q BQ_of_Z \0z +q \1q.
  rewrite (BQsum_0l QS1).
  by apply/(BQdiv_lt1P aq QpsS1 bqps); rewrite (BQdiv_x1 aq).
symmetry; apply: (BQ_floorp2 (proj32 pb) ZS0 (conj pb pc)).
Qed.

Lemma BQfloor_pos x  (m := BQfloor x): inc x BQp ->
  ( BQ_of_Z m = BQ_of_nat (P m) /\ natp (P m)).
Proof.
move => xp; move: (QpS_floor xp) => mzp.
split; first by rewrite /BQ_of_nat (BZp_hi_pr mzp). 
exact: (BZ_valN (BZp_sBZ mzp)).
Qed.

Lemma BQfloor_pos2 x (y := BQ_of_nat (P (BQfloor x))):
   inc x BQp -> y <=q x /\  x <q y +q \1q. 
Proof.
move => xp; move:(BQfloor_pos xp) => [sa sb].
by move:(BQ_floorp (BQp_sBQ xp)); rewrite sa.
Qed.

(** ** half and middle *)

Definition BQhalf x := x *q \2hq.
Definition BQmiddle x y := BQhalf (x +q y).

Lemma BQdouble_half2:  \2hq +q  \2hq = \1q.
Proof.
rewrite (BQdouble_p QSh2) - BQinv_2; apply:(BQdiv_xx QS2 BQ2_nz).
Qed.

Lemma QS_half x:  ratp x -> ratp (BQhalf x).
Proof. move => h ; apply (QSp h QSh2). Qed.

Lemma QS_middle x y:  ratp x -> ratp y -> inc (BQmiddle x y) BQ.
Proof. by move => xq yq; apply:QS_half; apply: QSs. Qed.

Lemma BQdouble_half1 x: ratp x -> BQhalf x +q BQhalf x = x.
Proof.
move => h.
by rewrite /BQhalf - (BQprodDr h QSh2 QSh2) BQdouble_half2 (BQprod_1r h).
Qed.


Lemma BQdouble_half x: ratp x -> BQdouble (BQhalf x) = x.
Proof. 
by move => h; rewrite - (BQdouble_p (QS_half h)) (BQdouble_half1 h).
Qed.

Lemma BQhalf_double x: ratp x -> BQhalf (BQdouble x) = x.
Proof.  
move => xQ; rewrite /BQhalf  - BQinv_2.  
apply:(BQdiv_prod QS2 xQ BQ2_nz).
Qed.

Lemma BQhalf_pos x: inc x BQps -> inc (BQhalf x) BQps. 
Proof. move => h; apply:(QpsS_prod h QpsSh2). Qed.

Lemma BQhalf_pos1 x: inc x BQps ->  (BQhalf x) <q x.
Proof.
move => h; move:(BQhalf_pos  h) => h1.
rewrite - {2} (BQdouble_half1 (BQps_sBQ h)).
apply: (BQsum_Mps (BQps_sBQ h1) h1).
Qed.

Lemma BQmiddle_comp x y: x <q y -> x <q BQmiddle x y /\  BQmiddle x y <q y.
Proof.
move => cp. 
move: (cp) => [[xq yq _] _].
split.
  have : BQdouble x <q x +q y.
    by rewrite - (BQdouble_p xq); apply /(BQsum_lt2l xq yq xq).
  move /(BQprod_plt2r (QSdouble xq) (QSs xq yq) QpsSh2).
  by rewrite -/(BQhalf (BQdouble x)) (BQhalf_double xq).
have : x +q y <q BQdouble y.
  by rewrite - (BQdouble_p yq); apply /(BQsum_lt2r xq yq yq).
move /(BQprod_plt2r (QSs xq yq) (QSdouble yq) QpsSh2).
by rewrite -/(BQhalf (BQdouble y)) (BQhalf_double yq).
Qed.


Lemma BQ_middle_prop1 a b: ratp a -> ratp b ->
   b -q (BQmiddle a b) = BQhalf (b -q a).
Proof.
move => aq bq; rewrite /BQmiddle -{1} (BQhalf_double bq) /BQhalf.
rewrite - (BQprodBl QSh2 (QSdouble bq) (QSs aq bq)). 
by rewrite -/(BQdouble b) - (BQdouble_p bq) BQdiff_sum_simpl_r.
Qed.

Lemma BQ_middle_prop2 a b: ratp a -> ratp b ->
   (BQmiddle a b) -q a = BQhalf (b -q a).
Proof.
move => aq bq.
rewrite /BQmiddle -{2} (BQhalf_double aq) /BQhalf.
rewrite - (BQprodBl QSh2 (QSs aq bq)(QSdouble aq)). 
by rewrite -/(BQdouble _) - (BQdouble_p aq) BQdiff_sum_simpl_l.
Qed.


Lemma BQhalf_prop x: BQhalf x = x /q \2q.
Proof. by rewrite /BQhalf - BQinv_2. Qed.

Lemma BQhalf_mon x y : x <=q y -> BQhalf x <=q BQhalf y.
Proof.
move => h.
by move/(BQprod_ple2r (proj31 h) (proj32 h) QpsSh2):h.
Qed.


Definition qsum f n := induction_term (fun n v => (f n) +q v) \0q n.
Definition rat_below f n := forall i, i<c n -> inc (f i) BQ.
Definition same_below (e e': fterm) n:= (forall i, i <c n -> e i = e' i).

Lemma qsum0 f: qsum f \0c = \0q.
Proof. by apply:induction_term0. Qed.

Lemma qsum_rec f n: natp n -> 
   qsum f (csucc n) =  f n +q  qsum f n.
Proof. by apply:induction_terms. Qed.

Lemma qsum1 f: inc (f \0c) BQ -> qsum f \1c = f \0c.
Proof. 
by move => h; rewrite - succ_zero (qsum_rec _ NS0) qsum0 BQsum_0r. Qed.


Lemma qsum_exten f g n: natp n -> same_below f g n -> qsum f n = qsum g n.
Proof.
move:n;apply: Nat_induction; first by move => _; rewrite !qsum0.
move => n nN Hrec h1; rewrite (qsum_rec f nN)  (qsum_rec g nN).
congr (_ +q _).
  by apply: h1; apply: cltS.
by apply: Hrec => i [/(cltSleP nN) /h1]. 
Qed.


Lemma QS_qsum f n: natp n -> rat_below f n -> ratp (qsum f n).
Proof.
move:n;apply: Nat_induction.
  move => _; rewrite qsum0; apply: QS0.
move => n nN Hrec h1; rewrite (qsum_rec f nN); apply: QSs.
  by apply: h1; apply: cltS.
by apply: Hrec => i [/(cltSleP nN) /h1]. 
Qed.

Lemma qsum_An f n m: natp n -> natp m ->
  (rat_below f (n +c m)) ->
  qsum f (n +c m) = (qsum f n) +q (qsum (fun i => f (n +c i)) m).
Proof.
move => nN hb; move: m hb; apply: Nat_induction.
  by rewrite (Nsum0r nN) qsum0 => /(QS_qsum nN) sq; rewrite BQsum_0r.
move => m mN Hrec h1.
have ha := (NS_sum nN mN).
have hb: inc (f (n +c m)) BQ by apply: h1; rewrite (csum_nS _ mN);apply: cltS.
have hc: inc (qsum f n) BQ. 
  apply:(QS_qsum nN) => i lin; apply: h1; rewrite (csum_nS n mN).
  exact: (clt_ltT (clt_leT lin (csum_M0le m (CS_nat nN)))  (cltS ha)).
have hd: inc (qsum (fun i => f (n +c i)) m) BQ.
  apply:(QS_qsum mN) => i lin; apply: h1.
  apply:(csum_Meqlt nN); exact: (clt_ltT lin (cltS mN)).
have he:  forall i, i <c n +c m -> inc (f i) BQ.
  move => i lin; apply: h1;rewrite  (csum_nS n mN).
  exact: (clt_ltT lin (cltS ha)).
rewrite (csum_nS _ mN) (qsum_rec _ ha) (Hrec he) (qsum_rec _ mN). 
rewrite (BQsumA hb hc hd) (BQsumA hc hb hd) (BQsumC (f (n +c m))) //.
Qed.

Lemma qsum_An1 f m: natp m ->
  (rat_below f (csucc m)) ->
  qsum f (csucc m) = (f \0c) +q (qsum (fun i => f (csucc i)) m).
Proof.
move => mN Ha.
have f0q: inc (f \0c) BQ by apply: Ha; apply: succ_positive.
move: Ha; rewrite (Nsucc_rw  mN) csumC => Ha.
rewrite (qsum_An NS1 mN Ha) (qsum1 f0q); congr( _ +q _).
by apply:(qsum_exten mN) => i lim; rewrite (Nsucc_rw (NS_lt_nat lim mN)) csumC.
Qed.

Lemma qsum_rev f n: natp n -> rat_below f n ->
  qsum f n  = qsum (fun i => f (n -c (csucc i))) n. 
Proof.
move => nN; move: n nN f; apply: Nat_induction.
  by move => f _; rewrite !qsum0.
move => n nN Hrec f fp;  move: (cltS nN) => sa.
have ->: qsum (fun i => f (csucc n -c csucc i)) (csucc n)
  = qsum (fun i => f (n -c i)) (csucc n).
  apply:(qsum_exten (NS_succ nN)) => i lin; rewrite cdiff_pr6 //.
  by apply: (NS_lt_nat lin (NS_succ nN)).
have ha: forall i, i <c csucc n -> inc (f (n -c i)) BQ.
  move => i lin; apply: fp; apply /(cltSleP nN); apply:cdiff_le1; fprops.
rewrite (qsum_rec _ nN)  (qsum_An1 nN ha) (cdiff_n0 nN) Hrec //.
by move => i lin;apply: fp;  apply:(clt_ltT lin sa).
Qed.

Lemma qsum_one f n: natp n -> (forall i, i<c n -> f i = \1q) ->
   qsum f n = BQ_of_nat n.
Proof.
move: n; apply: Nat_induction; first by move => _; rewrite qsum0.
move => n nN Hrec fp; move: (cltS nN) => aux.
rewrite (qsum_rec _ nN)(Nsucc_rw nN) csumC - (BQsum_cN NS1 nN) (fp _  aux).
congr (_ +q _); apply: Hrec => i lin; apply: fp; apply:(clt_ltT lin aux).
Qed.

Lemma qsum_sum f1 f2 n: natp n -> 
  rat_below f1 n -> rat_below f2 n ->
  qsum f1 n +q qsum f2 n = qsum (fun i => (f1 i +q f2 i)) n.
Proof.
move:n; apply: Nat_induction; first by rewrite !qsum0 (BQsum_0r QS0).
move => n nN Hrec f1p f2p.
have h := (cltS nN).
have ha: rat_below f1 n. move => i lin; apply: f1p; exact: (clt_ltT lin h).
have hb: rat_below f2 n by move => i lin; apply: f2p; exact: (clt_ltT lin h).
have hc: inc (qsum f1 n) BQ by apply:(QS_qsum nN). 
have hd: inc (qsum f2 n) BQ by apply:(QS_qsum nN).
by rewrite !(qsum_rec _ nN) (BQsum_ACA (f1p _ h) hc (f2p _ h) hd) Hrec. 
Qed.

Lemma qsum_even_odd f n: natp n -> 
  rat_below f (cdouble n) ->
  qsum f (cdouble n) = qsum (fun i => f (cdouble i)) n +q 
     qsum (fun i => f (csucc(cdouble i))) n.
Proof.
move: n; apply: Nat_induction; first by rewrite cdouble0 !qsum0 (BQsum_0r QS0).
move => n nN Hrec fp.
move: (NS_double nN) => dN; move:(NS_succ dN) (NS_succ nN) => sdN snN.
move: (cltS nN) => lt1.
move/(double_monotone2 nN snN): (lt1) => lt2.
have ha:  inc (f (cdouble n)) BQ by apply:fp. 
have hb: inc (f (csucc (cdouble n))) BQ.
  by apply:fp; apply /(double_monotone3  nN snN).
have hc:inc (qsum (fun i => f (cdouble i)) n) BQ.
  apply:(QS_qsum nN) => i lin;apply: fp. 
  apply /(double_monotone2 (NS_lt_nat lin nN) snN); exact: (clt_ltT lin lt1).
have hd: inc (qsum (fun i => f (csucc (cdouble i))) n) BQ.
  apply:(QS_qsum nN) => i lin;apply: fp. 
  apply /(double_monotone3 (NS_lt_nat lin nN) snN);  exact: (clt_ltT lin lt1).
have he: rat_below f (cdouble n). 
   move=> i lin;apply: fp; exact: (clt_ltT lin lt2).
have hf:=(QS_qsum dN he).
rewrite (double_succ nN) (qsum_rec _ sdN) (qsum_rec _ dN) ! (qsum_rec _ nN). 
rewrite (BQsum_ACA ha hc hb hd) (BQsumA hb ha hf) (BQsumC (f _)) Hrec //.
Qed.


End RationalNumbers.
Export  RationalNumbers.
