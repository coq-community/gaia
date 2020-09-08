(** * Theory of Sets EIII-5  Properties of integers
  Copyright INRIA (2009-2018) Apics; Marelle Team (Jose Grimm).
*)
(* $Id: sset9.v,v 1.6 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat binomial div.

Require Export sset8.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module IntegerProps.

(** ** EIII-5-1 Operations on integers and finite sets*)

(** Functions on nat *)  

Lemma Nsum_M0le a b: natp a -> a <=c (a +c b).
Proof. by move=> /CS_nat ca; apply: csum_M0le. Qed.

Lemma Nsum_Mle0 a b: natp a -> a <=c (b +c a).
Proof. by rewrite csumC; apply:Nsum_M0le. Qed.

Lemma Nprod_M1le a b: natp a -> b <> \0c -> a <=c (a *c b).
Proof. by move=> /CS_nat ca ; apply: cprod_M1le. Qed.

Lemma NleT_ell a b: natp a -> natp b ->
  [\/ a = b, a <c b | b<c a].
Proof. move=> aN bN; apply: cleT_ell; fprops. Qed.

Lemma NleT_el a b: natp a -> natp b ->
  a <=c b \/ b <c a.
Proof. move=> aN bN; apply: cleT_el; fprops. Qed.

Lemma NleT_ee a b: natp a -> natp b ->
  a <=c b \/ b <=c a.
Proof. move=> aN bN; apply: cleT_ee; fprops. Qed.

Lemma induction_sum0  f a b:  (~ inc b a) ->
  csum (restr f (a +s1 b)) =
  csum (restr f a) +c  (Vg f b).
Proof. move => nba; exact: (csumA_setU1 (Vg f) nba). Qed.

Lemma induction_prod0 f a b: (~ inc b a) ->
  cprod (restr f (a +s1 b)) =
  (cprod (restr f a)) *c (Vg f b) .
Proof. move => nba; exact: (cprodA_setU1 (Vg f) nba). Qed.

Lemma induction_sum1 f a b: 
  domain f = a +s1 b -> (~ inc b a) -> 
  csum f = csum (restr f a) +c (Vg f b).
Proof. by move=> df nba; rewrite - (induction_sum0 _ nba) -df - csum_gr. Qed.

Lemma csum_fs f n: natp n -> csumb (csucc n) f = csumb n f +c (f n).
Proof.
move => nN.
rewrite (succ_of_nat nN) /osucc /csumb.
have eq0: domain (Lg (n +s1 n) f) = (n +s1 n) by aw.
have n1:= (Nat_decent nN).
have n2: inc n (n +s1 n) by fprops.
have n3: sub n (n +s1 n) by fprops.
by rewrite (induction_sum1 eq0 n1) restr_Lg // LgV.
Qed.

Lemma csumb0 (f: fterm) : csumb \0c f = \0c.
Proof. by rewrite /csumb csum_trivial; aw. Qed.

Lemma csumb1 (f: fterm):  csumb \1c f = cardinal (f \0c).
Proof. by rewrite - succ_zero (csum_fs _ NS0) csumb0 csum_0l. Qed.

Lemma induction_prod1 f a b: 
  domain f = a +s1 b -> (~ inc b a) ->
  cprod f = cprod (restr f a) *c (Vg f b).
Proof. by move=> df nba; rewrite - (induction_prod0  _ nba) - df - cprod_gr. Qed.

(** Definition of a finite family of integers *)


Definition finite_int_fam f:= 
  (allf f natp) /\ finite_set (domain f).

(** A finite sum or product of integers is an integer *)

Section FiniteIntFam.
Variable f: Set.
Hypothesis fif: finite_int_fam f.

Lemma finite_sum_finite_aux x:
  sub x (domain f) -> natp (csum (restr f x)).
Proof. 
move: fif => [alN fsd] sxd.
have fsx:= (sub_finite_set sxd fsd).
move: x fsx sxd; apply: finite_set_induction0.
  move=> _;rewrite csum_trivial;aww.
move=> a b ap nba st;rewrite (induction_sum0 _ nba).
apply: NS_sum; [apply: ap; apply: sub_trans st | ];fprops. 
Qed.

Lemma finite_product_finite_aux x:
  sub x (domain f) -> natp (cprod (restr f x)).
Proof.
move: fif => [alN fsd] sxd.
have fsx:=(sub_finite_set sxd fsd).
move: x fsx sxd; apply: finite_set_induction0.
  rewrite cprod_trivial;fprops; aww.
move=> a b ap nba st; rewrite induction_prod0 =>//. 
apply:NS_prod;[apply: ap; apply: sub_trans st | ];fprops.
Qed.

Theorem finite_sum_finite: natp (csum f).
Proof.
rewrite - csum_gr;apply: finite_sum_finite_aux;fprops.
Qed.


Theorem finite_product_finite: natp (cprod f).
Proof.
rewrite - cprod_gr; apply: finite_product_finite_aux; fprops. 
Qed.

End FiniteIntFam.

(** Finite unions and products of finite sets are finite sets *)

Lemma finite_union_finite f: 
  (allf f finite_set) -> finite_set (domain f) -> finite_set (unionb f).
Proof. 
move=> alf fsd.
set (g:= Lg (domain f) (fun a  => cardinal (Vg f a))).
have dg: domain g = domain f by rewrite /g; aw.
have fif: finite_int_fam g.
  hnf; rewrite /allf dg /g; split => //i idf.
  by rewrite LgV //;apply /NatP; apply: alf. 
move: (csum_pr1 f) (finite_sum_finite fif) => f2 xN.
by apply/card_finite_setP; apply: (NS_le_nat f2).
Qed.

Lemma finite_product_finite_set f: 
  (allf f finite_set) -> finite_set (domain f) -> finite_set(productb f).
Proof. 
move=> alf fsd. 
set (g:= Lg (domain f) (fun a => cardinal (Vg f a))).
have dg: (domain g = domain f) by rewrite /g;aw.
rewrite/finite_set -/(cprod _) cprod_pr; apply: Nat_hi.
apply: finite_product_finite; split; last ue.
by hnf; aw; move=> i idf; rewrite LgV //; apply /NatP;apply: alf. 
Qed.


(** ** EIII-5-2 Strict inequalities between integers *)
(** If a<b there is a strictly positive c such that [b=a+c] *)

Lemma strict_pos_P1 a: natp a -> (a <> \0c <-> \0c <c a).
Proof.  
move => aN; split; [ apply : card_ne0_pos; fprops | by case => _ /nesym].
Qed.

Lemma strict_pos_P a: natp a -> (\0c <> a <-> \0c <c a).
Proof. 
move => aN; split; [ move /nesym; apply:card_ne0_pos; fprops | by case ].
Qed.

Lemma csum_M0lt a b: natp a -> b <> \0c -> a <c a +c b.
Proof.
move => aN bnz.
move: (cltS aN); rewrite - csum2cr (Nsucc_rw aN) => asa.
apply: (clt_leT asa); apply: csum_Meqle; apply: cge1; fprops.
by move/card_nonempty.
Qed. 

Lemma card_ltP1 a b: natp b -> a <c b ->  
   exists c, [/\ natp c, c <> \0c & a +c c = b].
Proof.
move=> bN [ab nab]; move: (NS_diff a bN) => pa; exists (b -c a); split => //.
  by apply: cdiff_nz.
by rewrite (cdiff_pr ab).
Qed.

Theorem card_ltP a b: natp a -> natp b ->
  (a <c b <->  exists c, [/\ natp c, c <> \0c & a +c c = b]).
Proof. 
move=> aN bN; split; first by apply:card_ltP1. 
move=> [c [cN cnz <-]] ;apply:csum_M0lt; fprops.
Qed.

(** Compatibility of sum and product with strict order  *)

Lemma csum_Meqlt a a' b: natp b ->
  a <c a' -> (b +c a) <c (b +c a').
Proof.
move => bN la; move:b bN; apply: Nat_induction.
  by rewrite (csum0l (proj31_1 la)) (csum0l (proj32_1 la)).
by move => n nN hr; rewrite (csum_Sn _ nN) (csum_Sn _ nN);apply: cltSS.
Qed.

Lemma csum_Mlelt a b a' b': natp a' -> 
  a <=c a' -> b <c b' -> (a +c b) <c (a' +c b').
Proof. 
move=> a'N aa' bb'. 
exact: (cle_ltT (csum_Mleeq b aa') (csum_Meqlt a'N  bb')).
Qed.

Lemma csum_Mlteq a a' b: natp b ->
  a <c a' -> (a +c b) <c (a'+c b).
Proof. 
by move=> bN aa'; rewrite csumC (csumC a' b); apply: csum_Meqlt.
Qed.

Lemma cprod_Meqlt a b b':
  natp a -> natp b' -> b <c b' -> a <> \0c ->
  (a *c b) <c (a *c b').
Proof.
move => aN b'N lt anz; move: (NS_lt_nat lt b'N) => bN.
move: (card_ltP1 b'N lt) => [c [cN cnz <-]].
rewrite cprodDr; apply:(csum_M0lt (NS_prod aN bN) (cprod2_nz anz cnz)).
Qed.

Lemma cprod_Mlelt a b a' b': natp a' -> natp b' ->
  a <=c a' -> b <c b' -> a' <> \0c ->
  (a *c b) <c (a' *c b').
Proof. 
move=> a'N b'N aa' bb' anz.
apply: (cle_ltT (cprod_Mleeq b aa') (cprod_Meqlt a'N b'N bb' anz)).
Qed.


Lemma cprod_M1lt a b: natp a -> 
  a <> \0c -> \1c <c b -> a <c (a *c b).
Proof. 
move => aN anz lt1b; move: a aN anz; apply: Nat_induction => //.
move => n nN hrec _; rewrite cprodC (cprod_via_sum _ (CS_nat nN)) cprodC.
case: (equal_or_not n \0c) => h.
  by rewrite h succ_zero cprod0l (csum0l (proj32_1 lt1b)).
move: (csum_Mlteq NS1 (hrec h));rewrite -(Nsucc_rw nN) => h2.
by apply:(clt_leT h2); apply:(csum_Meqle _ (proj1 lt1b)).
Qed.

Lemma cprod_ge1 a b: natp a -> natp b -> \1c <=c a *c b ->
  (\1c <=c a) /\ (\1c <=c b).
Proof.
move => aN bN pg1.
have pnz:=(proj2 (clt_leT clt_01 pg1)).
case: (equal_or_not a \0c) => az; first by case: pnz; rewrite az cprod0l.
case: (equal_or_not b \0c) => bz; first by case: pnz; rewrite bz cprod0r.
by split; apply: cge1 => //; apply CS_nat.
Qed.

Lemma cprod_M1lt' a b: natp a -> \1c <=c a -> \1c <c b -> a <c a *c b.
Proof.
move => aN la lb.
have anz:=(nesym (proj2 (clt_leT clt_01 la))). 
apply:(cprod_M1lt aN anz lb).
Qed.

Theorem finite_sum_lt f g:
  finite_int_fam f -> finite_int_fam g -> domain f = domain g -> 
  (forall i, inc i (domain f) -> (Vg f i) <=c  (Vg g i)) ->
  (exists2 i, inc i (domain f) &  (Vg f i) <c (Vg g i)) ->
  (csum f) <c (csum g).
Proof.
move=> [f2 f3] [g2 g3] df ale [i ifg lti].
have idg: inc i (domain g) by rewrite -df.
have dtc:=(sym_eq (setC1_K ifg)).
have incd: ~ (inc i ((domain f) -s1 i)).
  by move=> /setC1_P [_ ]; aw. 
have sd: sub ((domain f) -s1 i) (domain f) by apply: sub_setC.
have sdg: sub ((domain g) -s1 i) (domain g) by apply: sub_setC.
rewrite (induction_sum1 dtc incd).
rewrite df in dtc incd; rewrite (induction_sum1 dtc incd).
apply: csum_Mlelt lti.
  by apply: finite_sum_finite_aux.
 apply: csum_increasing; fprops; aww; first by ue.
move=> x xd;rewrite !LgV// - ?df;fprops. 
Qed.

Theorem finite_product_lt f g: 
  finite_int_fam f -> finite_int_fam g -> domain f = domain g ->
  (forall i, inc i (domain f) -> (Vg f i) <=c (Vg g i)) ->
  (exists2 i, inc i (domain f) & (Vg f i) <c (Vg g i)) ->
  card_nz_fam g ->
  (cprod f) <c (cprod g).
Proof. 
move=> [f2 f3] [g2 g3]  df ale [i ifg lti] alne.
have idg: inc i (domain g) by rewrite -df.
have afN: natp (Vg f i) by apply: f2. 
have agN: natp (Vg g i) by apply: g2. 
have sd: sub ((domain f) -s1 i) (domain f) by apply: sub_setC.
have sdg: sub ((domain g) -s1 i) (domain g) by apply: sub_setC.
have incd: ~ (inc i ((domain f) -s1 i)).
  by move=> /setC1_P [_ ]; aw => aux; case: aux.
move: (setC1_K ifg) => /esym dtc.
rewrite (induction_prod1 dtc incd).
rewrite df in dtc incd; rewrite (induction_prod1 dtc incd).
apply: cprod_Mlelt =>//.
+ by apply: finite_product_finite_aux. 
+ apply: cprod_increasing;aww; first by ue.
  move=> x xd; rewrite !LgV//  - ?df;fprops. 
+ apply/cprod_nzP; fprops; hnf;aw => j jdg. 
  move: (jdg) => /setC1_P [jd _]; rewrite LgV//;apply: (alne _ jd).
Qed.


(** Compatibility of power and order *)

Lemma cpow_nz a b: a <> \0c -> (a ^c b) <> \0c.
Proof. 
move=> anz;rewrite - cprod_of_same; apply /cprod_nzP.
by hnf; aw => t tb; rewrite LgV. 
Qed.

Lemma cpow2_nz x: \2c ^c x <> \0c.
Proof. apply: cpow_nz; fprops. Qed.

Lemma cpow2_pos x: \0c <c \2c ^c x.
Proof. apply (card_ne0_pos (CS_pow _ _) (@cpow2_nz _)). Qed.

Lemma cpow_Mltle a a' b:
  natp a' -> natp b -> a <c a' -> b <> \0c ->  (a ^c b) <c (a' ^c b).
Proof. 
move=> a'N bN aa' nzb.
move:b bN nzb; apply:Nat_induction => // n nN hrec _.
case: (equal_or_not n \0c) => nz.
   by rewrite nz succ_zero (cpowx1 (proj31_1 aa')) (cpowx1 (proj32_1 aa')).
rewrite (cpow_succ _ nN) (cpow_succ _ nN).
apply:(cprod_Mlelt (NS_pow a'N nN) a'N (proj1 (hrec nz)) aa'). 
exact: (cpow_nz (card_gt_ne0 aa') (b:=n)).
Qed.

Lemma cpow_Meqlt a b b':
  natp a -> natp b' ->
  b <c b' -> \1c <c a ->  (a ^c b) <c (a ^c b').
Proof.
move=> aN b'N bb' l1a.
have anz := card_gt_ne0 l1a.
have bN:= NS_lt_nat bb' b'N.
have [c [cN cnz <-]]:= (card_ltP1 b'N bb').
have le1 := (clt_leT l1a (cpow_Mle1 (CS_nat aN) cnz)). 
rewrite cpow_sum2; apply: cprod_M1lt;fprops; apply: (cpow_nz anz).
Qed.

Lemma cpow2_MeqltP n m: natp n -> natp m ->
    (\2c ^c n <c \2c ^c m <-> n <c m).
Proof.
move => sa sb; split => h; last apply: (cpow_Meqlt NS2 sb h clt_12).
by case: (NleT_el sb sa) => // /cpow_M2le /(cltNge h).
Qed.

Lemma cpow_M1lt a b: cardinalp a -> \1c <c b ->  a <c (b ^c a).
Proof. 
move => ca /(cleSltP NS1); rewrite succ_one => h.
apply: (clt_leT (cantor ca)); apply:(cpow_Mleeq _ h card2_nz).
Qed. 

(** Injectivity of sum and product  *)

Section Simplifications.
Variables (a b b' :Set).
Hypotheses (aN: natp a) (bN: natp b) (b'N: natp b').

Lemma csum_eq2l:  a +c b = a +c b' -> b = b'.
Proof. 
move=> eql.
case: (NleT_ell bN b'N) =>// aux. 
  by case: (proj2 (csum_Meqlt aN aux)).
by case: (proj2 (csum_Meqlt aN aux)).
Qed.

Lemma csum_eq2r: b +c a = b' +c a -> b = b'.
Proof. by rewrite csumC (csumC b' a); apply: csum_eq2l. Qed.

Lemma cprod_eq2l: a <> \0c -> a *c b = a *c b' -> b = b'.
Proof.
move=> naz eql.
case: (NleT_ell bN b'N) =>// aux.
  by case: (proj2 (cprod_Meqlt aN b'N aux naz)).
by case: (proj2(cprod_Meqlt aN bN aux naz)).
Qed.

Lemma cprod_eq2r: a <> \0c -> b *c a = b' *c a -> b = b'.
Proof. by rewrite cprodC (cprodC b' a);apply: cprod_eq2l. Qed.

End Simplifications.


(** cardinal difference *) 

Lemma cdiff_rpr a b: b <=c a -> (a -c b) +c b = a.
Proof. by move=> /cdiff_pr ;rewrite csumC. Qed.

Lemma cdiff_pr2 a b c: natp a -> natp b ->
  a +c b = c -> c -c b = a.
Proof. by move=> aN bN h; move: (cdiff_pr1 aN bN); rewrite h. Qed.

Lemma cdiff_pr3 a b n:
   natp n -> a <=c b -> b <=c n -> (n -c b) <=c (n -c a).
Proof.
move => mN le1 le2.
have bN:=(NS_le_nat le2 mN).
have aN:=(NS_le_nat le1 bN).
have dN:=(NS_sum (NS_diff a bN) (NS_diff b mN)).
rewrite - {2} (cdiff_pr le2)  -{2} (cdiff_pr le1). 
rewrite - csumA (csumC a) (cdiff_pr1 dN aN); apply:(csum_Mle0 _ (CS_diff n b)).
Qed.


Lemma cdiff_pr7 a b c:
  a <=c b -> b <c c -> natp c -> (b -c a) <c (c -c a).
Proof.
move => le1 lt2 cN.
have bN:= (NS_lt_nat lt2 cN).
have aN:= (NS_le_nat le1 bN).
move:(NS_diff a bN) (NS_diff b cN) => ha hb.
rewrite -(cdiff_pr (proj1 lt2)) - {2}(cdiff_pr le1) - csumA csumC.
rewrite (cdiff_pr1 (NS_sum ha hb) aN);apply: (csum_M0lt ha (cdiff_nz lt2)).
Qed.

Lemma cdiff_pr8 n p q: q <=c p -> p <=c n -> natp n ->
  (n -c p) +c q = n -c (p -c q).
Proof.
move => leqp lepn  nN.
have pN := NS_le_nat lepn nN.
have qN := NS_le_nat leqp pN.
rewrite - {2} (cdiff_pr lepn) -{2} (cdiff_pr leqp) [in RHS] csumC.
by rewrite csumA (cdiff_pr1 (NS_sum (NS_diff p nN) qN)  (NS_diff q pN)).
Qed.

Lemma cdiffA2 a b c: natp a -> natp b ->
  c <=c a -> (a +c b) -c c  = (a -c c) +c b.
Proof.
move => aN bN h.
move:(NS_sum (NS_diff c aN) bN) (NS_le_nat h aN) => pa pb.
rewrite - {1} (cdiff_pr h)  - csumA (csumC c) cdiff_pr1 //.
Qed.

Lemma cdiffSn a b: natp a -> b <=c a ->
   (csucc a) -c b = csucc (a -c b).
Proof.
move => aN leab.
rewrite (Nsucc_rw aN) (Nsucc_rw (NS_diff b aN)); apply: (cdiffA2 aN NS1 leab).
Qed.

Lemma cardinal_setC4 E A: sub A E -> 
  finite_set E -> cardinal (E -s A) = (cardinal E) -c (cardinal A).
Proof.
move => AE /NatP sN.
have cc:= (cardinal_setC AE); rewrite - cc in sN.
symmetry; rewrite - cc csumC;apply: cdiff_pr1. 
  exact: (NS_in_sumr  (CS_cardinal (E -s A)) sN).
exact:(NS_in_suml (CS_cardinal A) sN).
Qed.

Lemma cdiff_nn a: a -c a = \0c.
Proof. by rewrite /cdiff setC_v cardinal_set0.  Qed.

Lemma cardinal_setC5 A B: finite_set B -> sub A B -> A =c B -> A = B.
Proof.
move => fsB sAB cAB.
move: (cardinal_setC4 sAB fsB); rewrite cAB cdiff_nn.
by move /card_nonempty /empty_setC /(extensionality sAB).
Qed.

Lemma cdiff_0n n : \0c -c n = \0c.
Proof. by rewrite /cdiff (setC_T (sub0_set n)) cardinal_set0. Qed.

Lemma cdiff_pr4 a b a' b': natp a -> natp b ->
  natp a' -> natp b' ->
  a <=c b -> a' <=c b' ->
  (b +c b') -c (a +c a') = (b -c a) +c (b' -c a').
Proof. 
move=> aN bN a'N b'N ab a'b'.
have aux: ((b -c a) +c b') +c a = b' +c b.
  by rewrite (csumC _ b') - csumA cdiff_rpr.
apply: cdiff_pr2; fprops.
by rewrite (csumC a a') csumA - (csumA _ _ a') (cdiff_rpr  a'b') aux csumC.
Qed.

Lemma cdiffA a b c:
  natp a -> natp b -> natp c ->
  (b +c c) <=c a -> (a -c b) -c c = a -c (b +c c).
Proof.
move=> aN bN cN h.
have aux:= (cdiff_pr h).
apply: cdiff_pr2 =>//; first by fprops.
symmetry; apply: cdiff_pr2; fprops.
by rewrite - csumA csumC (csumC c b).  
Qed.

Lemma cpred_pr4 a: cardinalp a -> cpred a = a -c \1c.
Proof. 
move=> ca.
case: (Nat_dichot ca) => aN.
  case: (equal_or_not a \0c) => anz. 
    by rewrite anz cpred0 (cdiff_wrong cle_01).
  move:(cpred_pr aN anz) => [sa {2} ->].
  by rewrite (csucc_pr4 (CS_nat sa)) (cdiff_pr1 sa NS1).
by rewrite (cpred_inf aN) (cdiff_fin_infin finite_1 aN).
Qed. 

Lemma cpred_monotone a b: a <=c b -> cpred a <=c cpred b.
Proof.
move => [ca cb sab]; split; [exact (CS_pred ca) | exact (CS_pred cb) | ].
rewrite /cpred/opred => t /setU_P [y ya /sab yb]; union_tac.
Qed.

Lemma cdiff_lt_pred a b: natp b -> b <> \0c ->
   (a <c b <-> a <=c (b -c \1c)). 
Proof.
move => bN /(cpred_pr bN) [sa sb].
rewrite - (cpred_pr4 (CS_nat bN)) {1} sb;exact:(cltSleP sa).
Qed.

Lemma cdiff_nz1 a b: natp a -> natp b -> 
  (csucc b) <=c a -> a -c b <> \0c.
Proof.
move=> aN bN /(cleSltP bN) lesba; apply: cdiff_nz => //. 
Qed.

Lemma cdiff_A1 a b: natp a -> natp b -> 
  (csucc b) <=c a -> cpred (a -c b) = a -c (csucc b).
Proof.
move=> aN bN; rewrite (Nsucc_rw bN) => h'. 
rewrite - cdiffA; fprops; apply: cpred_pr4; fprops.
Qed.

Lemma cdiff_ab_le_a a b: cardinalp a -> (a -c b) <=c a.
Proof. 
by move => ca; move: (sub_smaller (@sub_setC a b)); rewrite (card_card ca).
Qed.

Lemma cdiff_ab_lt_a a b: natp a -> b <=c a -> b <> \0c ->
   a -c b <c a.
Proof.
move =>  bN leab anz.
split; first by apply: (cdiff_ab_le_a _ (CS_nat bN)).
move => dd; move:(proj2 (csum_M0lt bN anz)); rewrite csumC; case.
by move: (cdiff_pr leab); rewrite dd.
Qed.

Lemma cdiff_ltb a b: natp b -> a <=c b -> a <> \0c ->
   b -c a <c b.
Proof.
move =>  bN leab anz.
split; first by apply: (cdiff_ab_le_a _ (CS_nat bN)).
move => dd; move:(proj2 (csum_M0lt bN anz)); rewrite csumC; case.
by move: (cdiff_pr leab); rewrite dd.
Qed.

Lemma cdiff_lt_symmetry' n p: natp p -> p <> \0c ->  cpred (p -c n) <c p.
Proof.
move=> pN pnz.
exact: (cle_ltT (cpred_monotone (cdiff_le1 n (CS_nat pN))) (cpred_lt pN pnz)).
Qed.

Lemma cdiff_lt_symmetry n p: natp p -> 
  n <c p -> cpred (p -c n) <c p.
Proof. 
move=> pN ltnp; exact:(cdiff_lt_symmetry' n pN (card_gt_ne0 ltnp)).
Qed.

Lemma double_diff n p: natp n -> 
  p <=c n -> n -c (n -c p) = p.
Proof. 
move=> nN lepn.
have pN:= (NS_le_nat lepn nN).
exact: (cdiff_pr2 pN (NS_diff p nN) (cdiff_pr lepn)).
Qed.

Lemma csucc_diff a b: natp a -> natp b -> 
  (csucc b) <=c a -> a -c b = csucc (a -c (csucc b)).
Proof.
move=> aN bN aux; move: (NS_succ bN) => sN.
apply: cdiff_pr2; fprops.
have dN: natp (a -c (csucc b)) by fprops.
by rewrite (csum_Sn _ dN)  - (csum_nS _ bN); apply: cdiff_rpr.
Qed.



Lemma cdiff_pr5 a b c: cardinalp a -> cardinalp b -> natp c ->
  (a +c c) -c (b +c c) = a -c b.
Proof.
move => ca cb cN;move: c cN; apply: Nat_induction.
   rewrite !csum0r //.
move => n nN Hrec; rewrite (csum_nS _ nN) (csum_nS _ nN) cdiff_succ //; fprops.
Qed.

Lemma cdiff_pr6 a b: natp a -> natp b ->
  (csucc a) -c (csucc b) = a -c b.
Proof. by move => /CS_nat ca /CS_nat cb; apply:cdiff_succ. Qed.

Lemma cprodBl a b c: natp a -> natp b -> natp c ->
   a *c (b -c c) = (a *c b) -c (a *c c).
Proof. 
move=> aN bN cN.
case: (NleT_ee bN cN) => le.
  by rewrite (cdiff_wrong le) (cdiff_wrong (cprod_Meqle a le)) (cprod0r).
symmetry; apply: cdiff_pr2; fprops; rewrite - cprodDr csumC cdiff_pr //.
Qed.


Lemma cardinal_complement_image1 f (S := source f) (T := target f) :
  injection f ->
  (cardinal (T -s (Imf f))) +c (cardinal S) = cardinal T.
Proof.
move => injf.
set A:= (Imf f).
have ->: (cardinal S = cardinal A).
  apply /card_eqP;exists (restriction_to_image f).
  rewrite /restriction_to_image/restriction2; hnf;saw.
  by apply: (restriction_to_image_fb injf).
symmetry; rewrite csumC.
have p0: sub A T by apply: Imf_Starget; fct_tac.
rewrite - {1} (setU2_Cr p0) csum2cl csum2cr csum2_pr5 //;apply: set_I2Cr.
Qed.

Lemma cardinal_complement_image f (S := source f) (T := target f) :
  injection f -> finite_set T ->
  cardinal (T -s (Imf f)) = (cardinal T) -c (cardinal S).
Proof.
move=> injf /NatP fb.
have h:= (cardinal_complement_image1 injf).
rewrite - h in fb |- *.
have aN := (NS_in_sumr (CS_cardinal S) fb).
have cN:= (NS_in_suml (CS_cardinal (T -s Imf f)) fb).
by symmetry;apply: cdiff_pr1.
Qed.


Lemma csum_le2l' a b c : natp a -> cardinalp b -> cardinalp c ->
  (a +c b) <=c (a +c c) -> b <=c c.
Proof.
move => aN cb cc abc.
by case: (cleT_el cb cc) => // /(csum_Meqlt aN) /(cleNgt abc).
Qed.

Lemma csum_lt2l' a b c : natp a -> cardinalp b -> cardinalp c ->
  (a +c b) <c (a +c c) -> b <c c.
Proof.
move=> aN cb cc [abc nac]. 
split;[ apply: (csum_le2l' aN cb cc abc) | dneg bc; ue].
Qed.

  
Section Simplification.
Variables a b c: Set.
Hypothesis (aN: natp a) (bN: natp b) (cN: natp c).

Lemma csum_le2l: (a +c b) <=c (a +c c) -> b <=c c.
Proof. exact:(csum_le2l' aN (CS_nat bN) (CS_nat cN)). Qed.

Lemma csum_le2r: (b +c a) <=c (c +c a) -> b <=c c.
Proof. rewrite !(csumC _ a); apply:csum_le2l. Qed.

Lemma csum_lt2l: (a +c b) <c (a +c c) -> b <c c.
Proof.
move=> [abc nac]; split;[ apply: (csum_le2l abc) | dneg bc; ue].
Qed.

Lemma csum_lt2r: (b +c a) <c (c +c a) -> b <c c.
Proof. rewrite !(csumC _ a); apply:csum_lt2l. Qed.

Lemma cprod_le2l: a <> \0c ->  (a *c b) <=c  (a *c c) -> b <=c c.
Proof. 
move=>naz abc; case: (NleT_el bN cN) => // ltcb.
case: (cleNgt abc (cprod_Meqlt aN bN ltcb naz)).
Qed.

Lemma cprod_le2r: a <> \0c ->  (b *c a) <=c  (c *c a) -> b <=c c.
Proof. rewrite !(cprodC _ a); apply:cprod_le2l. Qed.


Lemma cprod_lt2l: (a *c b) <c  (a *c c) -> b <c c.
Proof. 
move=> [abc nac]; case: (equal_or_not a \0c) => anz.
  by case: nac; rewrite anz !cprod0l.
split; [ by apply: cprod_le2l |  move => bc;case: nac; ue].
Qed.

Lemma cprod_lt2r: (b *c a) <c  (c *c a) -> b <c c.
Proof. rewrite !(cprodC _ a); apply:cprod_lt2l. Qed.

End Simplification.


Lemma cdiff_pr9 n p q: natp n -> natp p -> natp q -> q <=c p ->
  (n <=c p -c q <-> n +c q <=c p).
Proof.
move => nN pN qN lqp.
rewrite - {2} (cdiff_pr lqp) csumC; split => h; first by apply:csum_Meqle.
apply:(csum_le2l qN nN (NS_diff _ pN) h).
Qed.

Lemma cdiff_Mle a b c: natp a -> natp b -> 
  c <=c (a +c b) -> (c -c b) <=c a.
Proof. 
move=> aN bN cab.
move: (NS_le_nat cab (NS_sum aN bN)) => cN.
case: (NleT_ee cN bN) => cb.
  rewrite (cdiff_wrong cb); exact (cle0n aN).
by apply: (csum_le2r bN (NS_diff b cN) aN); rewrite (cdiff_rpr cb).
Qed.

Lemma cdiff_Mlt a b c: natp a -> natp c ->
  b <=c c -> c <c (a +c b) ->  (c -c b) <c a.
Proof. 
move=> aN cN  bc cab. 
move: (NS_le_nat bc cN) => bN.
by apply: (csum_lt2r bN (NS_diff b cN) aN); rewrite (cdiff_rpr bc).
Qed.


Lemma cdiff_Mlt' a b c: natp a -> natp b ->
  a <> \0c -> c <c (a +c b) ->  (c -c b) <c a.
Proof. 
move=> aN bN anz cab. 
move: (NS_lt_nat cab (NS_sum aN bN)) => cN.
case: (NleT_ee cN bN) => cb.
  by rewrite (cdiff_wrong cb); apply/(strict_pos_P1 aN).
by apply: (csum_lt2r bN (NS_diff b cN) aN); rewrite (cdiff_rpr cb).
Qed.


(** ** EIII-5-3  Intervals in sets of integers *)

(* Properties of the Nat ordering *)

Definition Nat_order := graph_on cardinal_le Nat.
Definition Nat_le x y := [/\ natp x, natp y & x <=c y].
Definition Nat_lt x y := Nat_le x y /\ x<>y.

Notation "x <=N y" := (Nat_le x y) (at level 60).
Notation "x <N y" := (Nat_lt x y) (at level 60).

Lemma Nat_order_wor: worder_on Nat_order Nat.
Proof. by move: (wordering_cle_pr CS_nat). Qed.

Lemma Nat_order_leP x y: 
  gle Nat_order x y <-> x <=N y.
Proof. apply: graph_on_P1. Qed.


Lemma NleR a: inc a Nat -> a <=N a.
Proof. move => aN; split;fprops. Qed.

Lemma NleT a b c: a <=N b -> b <=N c -> a <=N c.
Proof. 
move /Nat_order_leP => ab  /Nat_order_leP bc; apply  /Nat_order_leP.
move: Nat_order_wor=> [[or wor] _]; order_tac. 
Qed.

Lemma NleA a b: a <=N b -> b <=N a -> a = b.
Proof. 
move /Nat_order_leP => ab  /Nat_order_leP ba.
move: Nat_order_wor=> [[or wor] _]; order_tac.
Qed.


Section NatIinterval.
Variables (a b: Set).
Hypotheses (aN: natp a) (bN: natp b).

Lemma Nint_ccP x:
  (inc x (interval_cc Nat_order a b) <-> (a <=N x /\ x <=N b)).
Proof.
rewrite /interval_cc (proj2 Nat_order_wor); split.
  by move /Zo_P => [xb [/Nat_order_leP pa  /Nat_order_leP pb]].
move => [pa pb]; apply /Zo_i; first by move: pa => [_].
by split; apply /Nat_order_leP.
Qed.

Lemma Nint_coP x:
  (inc x (interval_co Nat_order a b) <-> (a <=N x /\ x <N b)).
Proof. 
rewrite/ Nat_lt/interval_co (proj2 Nat_order_wor); split.
  by move /Zo_P => [xb []] /Nat_order_leP pa [] /Nat_order_leP pb xnb.
move => [pa [pb pc]]; apply /Zo_i; first by move: pa => [_].
by split; [| split => // ];apply /Nat_order_leP.
Qed.

Lemma Nint_ccP1 x:
  (inc x (interval_cc Nat_order a b) <-> (a <=c x /\ x <=c b)).
Proof.
apply: (iff_trans (Nint_ccP x)); split.
   by move=> [[_ _ pa] [_ _ pb]].
move=> [ax bx]; move:(NS_le_nat bx bN) => xN //.
Qed.

Lemma Nint_coP1 x: 
  (inc x (interval_co Nat_order a b) <-> (a <=c x /\ x <c b)).
Proof. 
apply: (iff_trans (Nint_coP x)); split.
  by move=> [[_ _ pa] [[_ _ pb] pc]].
move=> [ax [bx xb]];  move:(NS_le_nat bx bN) => xN //.
Qed.

End NatIinterval.

Definition Nintcc a b := interval_cc Nat_order a b.
Definition Nint a:= interval_co Nat_order \0c a.
Definition Nintc a:= Nintcc \0c a.
Definition Nint1c a:= Nintcc \1c a.

Definition Nint_cco a b := graph_on cardinal_le (Nintcc a b).

Lemma Nint_S a b: sub (Nintcc a b) Nat. 
Proof. by move => t /Zo_S; rewrite (proj2 Nat_order_wor). Qed.

Lemma Nint_S1 a:  sub (Nint a) Nat.
Proof. by move => t /Zo_S; rewrite (proj2 Nat_order_wor). Qed.

Lemma Nint1cPb b: natp b -> forall x,
  (inc x (Nint1c b) <-> (\1c <=c x /\ x <=c b)).
Proof. move=> aN x; apply: (Nint_ccP1 NS1 aN). Qed.

Lemma Nint1cP  b: natp b -> forall x,
  inc x (Nint1c b) <->  (x <> \0c /\ x <=c b).
Proof.
move=> bN x; apply: (iff_trans (Nint_ccP1 NS1 bN x)).
split; move => [pa pb]; split => //.
  exact: (nesym (proj2 (clt_leT clt_01 pa))).
exact: (cge1 (proj31 pb) pa).
Qed.

Lemma NintE n: natp n -> Nint n = n.
Proof.
move=> nN; have h := (Nint_coP1 NS0 nN).
set_extens t; first by move/h => [_ /(NltP nN)].
move/(NltP nN)=> ltn; apply/h; split => //;apply: (cle0x (proj31_1 ltn)).
Qed.

Lemma NintP a: natp a -> forall x,
  (inc x (Nint a) <-> x <c a).
Proof. by move=> aN x; rewrite (NintE aN); apply: iff_sym;apply: NltP. Qed.

Lemma NintcP b: natp b -> forall x, inc x (Nintc b) <-> x <=c b.
Proof. 
move=> bN x; split; first by move /Nint_ccP => [_ [_ _ h]].
by move => h;apply /(Nint_ccP1 NS0 bN); move: (cle0x (proj31 h)). 
Qed.

Lemma Nint_co_cc p: natp p -> Nintc p = Nint (csucc p).
Proof. 
move => pN;move:(NS_succ pN) => snP; rewrite (NintE snP);set_extens t.
- by move => /(NintcP pN) /(NleP pN).
- by move => /(NleP pN) /(NintcP pN).
Qed.

Lemma NintcE n: natp n -> Nintc n = csucc n.
Proof. by move=> nN; rewrite (Nint_co_cc nN) (NintE (NS_succ nN)). Qed.
  
Lemma NintsP a: natp a -> forall x,
  (inc x (Nint (csucc a)) <-> x <=c a).
Proof. move=> aN; rewrite - (Nint_co_cc aN); exact (NintcP aN). Qed.

Lemma Nint_co00: Nint \0c = emptyset.
Proof. by rewrite (NintE NS0). Qed.

Lemma Nint_co01: (inc \0c (Nint \1c) /\ Nint \1c = singleton \0c).
Proof.
rewrite (NintE NS1); split => //; apply: set1_1.
Qed.

Lemma Nint_cc00: Nintc \0c = singleton \0c.
Proof.
by rewrite -(proj2 Nint_co01) - succ_zero (Nint_co_cc NS0). 
Qed.

Lemma Nint_si a: natp a ->  inc a (Nint (csucc a)).
Proof. move=> aN; apply /(NintsP aN); fprops. Qed.

Lemma Nint_M a: natp a -> sub (Nint a) (Nint (csucc a)).
Proof. 
move => aN; rewrite (NintE aN) (NintE (NS_succ aN)) (succ_of_nat aN). 
apply:subsetU2l. 
Qed.

Lemma Nint_M1 a b: natp b -> a <=c b -> sub (Nint a) (Nint b).
Proof. 
by move=> bN ab; rewrite (NintE bN) (NintE (NS_le_nat ab bN)); case: ab.
Qed.

Lemma Nint_pr4 n: natp n ->
  ( ((Nint n) +s1 n = (Nint (csucc n))) /\ ~(inc n (Nint n))).
Proof. 
move=> nN; rewrite {1} (NintE nN) (NintE (NS_succ nN)) (succ_of_nat nN).
by split => //; case/(NintP nN).
Qed.

Lemma Nint_pr5 n (si := Nintcc \1c n): natp n ->
  ( (si +s1 \0c = Nintc n)  /\ ~(inc \0c si)).
Proof.
move=> nN; split. 
  set_extens x. 
    case /setU1_P; first by move /(Nint_ccP1 NS1 nN) => [_]/(NintcP nN).
    move => ->; apply /(NintcP nN); exact: (cle0n nN).
  move  /(NintcP nN) => h; apply /setU1_P.
  case: (equal_or_not x \0c) => xz; [ by right | left  ].
  apply /(Nint_ccP1 NS1 nN);split => //;apply: cge1 => //; exact: (proj31 h).
move /(Nint_ccP1 NS1 nN) => [ /cleNgt []]; fprops.
Qed.

Lemma incsx_intsn x n: natp n ->
  inc x (Nint n) -> inc (csucc x) (Nint (csucc n)).
Proof.
by move => nN;  move/(NintP nN) => /cltSS /(NintP (NS_succ nN)).
Qed.

Lemma inc0_int01: inc \0c (Nint \1c). 
Proof. by apply /NintP; fprops. Qed.

Lemma inc0_int02: inc \0c (Nint \2c). 
Proof. by apply /NintP; fprops; apply: clt_02. Qed.

Section IntervalNatwo.
Variables (a b: Set).
Hypotheses (aN: natp a)(bN: natp b).

Lemma Ninto_wor: worder_on (Nint_cco a b) (Nintcc a b).
Proof.
move: cle_wor => wo.
have r: (forall x, inc x (interval_cc Nat_order a b) -> x <=c x).
  move=> x xb; exact (cleR (CS_nat (Nint_S xb))).
by move: (wordering_pr wo r).
Qed.

Lemma Ninto_gleP  x y: 
  gle (Nint_cco a b) x y <-> 
    [/\ inc x (Nintcc a b), inc y (Nintcc a b) & x <=c y].
Proof. apply: graph_on_P1. Qed.

Lemma Ninto_gleP2 x y: 
  gle (Nint_cco a b) x y <->  [/\ a <=c x, y <=c b & x <=c y].
Proof. 
split.
  move/Ninto_gleP=> [] /(Nint_ccP1 aN bN) [pa pb] /(Nint_ccP1 aN bN) [pc pd] pe.
  done.
move => [pa pb pc]; move:(cleT pc pb)  (cleT pa pc) => pd pe.
by apply/Ninto_gleP; split => //; apply /(Nint_ccP1 aN bN). 
Qed.

End IntervalNatwo.

Definition Nint_co a := 
  graph_on cardinal_le (Nint a).

Section IntervalNatwo1.
Variable (a: Set).
Hypothesis (aN: natp a).

Lemma Nintco_wor: worder_on (Nint_co a) (Nint a).
Proof. 
move: cle_wor => wo. 
have r: forall x, inc x (Nint a) -> x <=c x.
  move=> x xi; move: (Nint_S1 xi) => xN; fprops.
by move: (wordering_pr wo r).
Qed.

Lemma Nintco_gleP x y: gle (Nint_co a) x y <-> (x <=c y  /\ y <c a).
Proof. 
split.
  by move /graph_on_P1 => [] /(NintP aN) xa /(NintP aN) ya xy. 
move=> [xy ya]; move:(cle_ltT xy ya)=> h. 
by apply/graph_on_P1; split => //;apply /(NintP aN).
Qed.

End IntervalNatwo1.


Lemma segment_Nat_order n: natp n ->
  segment Nat_order n = Nint n.
Proof. 
move=> xN; set_extens t;move /Zo_P => [pa pb];apply:Zo_i => //;last by case: pb.
move: pb => [ /Nat_order_leP [tn aa bb] cc].
move: NS0  (cle0x (proj31 bb)) => ha hb.
split; first by apply/Nat_order_leP.
by split; [  apply/Nat_order_leP | exact ].
Qed.


Lemma segment_Nat_order1 n: natp n -> segment Nat_order n = n.
Proof.
by move=> nN; rewrite (segment_Nat_order nN) (NintE nN).
Qed.

Definition rest_plus_interval a b :=
  Lf(fun z => z +c b)(Nintcc \0c a) (Nintcc b (a +c b)).

Definition rest_minus_interval a b :=
  Lf(fun z => z -c b) (Nintcc b (a +c b)) (Nintcc \0c a).

Theorem restr_plus_interval_is a b
        (f := (rest_plus_interval a b))
        (g := (rest_minus_interval a b)):
  natp a -> natp b ->
  [/\ bijection f,  bijection g, g = inverse_fun f &
   order_isomorphism f (Nint_cco \0c a) (Nint_cco b (a +c b))].
Proof. 
move=> aN bN.
have zN:= NS0.
have abN:= (NS_sum aN bN).
set E1:= Nintc a.
set E2:= Nintcc b (a +c b).
have tap: lf_axiom (fun z => z +c b) E1 E2.
  move => z /(NintcP aN) za; apply/(Nint_ccP1 bN abN); split.
   by apply: Nsum_Mle0.
  by apply: csum_Mleeq. 
have tam: lf_axiom (fun z => z -c b) E2 E1.
  move => z /(Nint_ccP1 bN abN) [bt tab]; apply /(NintcP aN).
  move: (NS_diff b (NS_le_nat tab abN)) => sN; apply: cdiff_Mle =>//.
have ff:function f by apply: lf_function. 
have fg:function g by apply: lf_function. 
have sf:source f = target g  by rewrite lf_source lf_target.
have sg:source g = target f  by rewrite lf_source lf_target.
have cfg:f \coP g by [].
have cgf: g \coP f by [].
have c1: g \co f = identity (source f).
  apply: function_exten; [fct_tac | fprops | by aw | by  aw | ].
  rewrite compf_s;move=> x xsf /=.
  rewrite (idV xsf) compfV //.
  move: xsf; rewrite lf_source=> xs. 
  rewrite (LfV tap xs) (LfV tam (tap _ xs)).
  rewrite cdiff_pr1 =>//; apply: (Nint_S xs).
have c2: f \co g = identity (source g).
  apply: function_exten ; [fct_tac | fprops | by aw | by  aw | ].
  rewrite compf_s;move=> x xsg /=.
  rewrite (idV xsg)  (compfV cfg xsg).
  move: xsg; rewrite lf_source=> xs. 
  rewrite (LfV tam xs).  
  have xN:=(Nint_S xs).
  move: xs => /(Nint_ccP1 bN abN) [bx xaN].
  have aux: inc (x -c b) (Nintcc \0c a).
    apply/(NintcP aN); apply: cdiff_Mle =>//.
  rewrite (LfV tap aux) csumC cdiff_pr //.  
move: (bijective_from_compose cgf cfg c1 c2)=> [bf bg gif]; split => //.
have sp : E1 = source (rest_plus_interval a b).
  by rewrite /rest_plus_interval; aw.
move: (Ninto_wor \0c a) => [[o1 _ ] sr1].  
move: (Ninto_wor b (a +c b))=> [[o2 _ ] sr2].
hnf;rewrite /bijection_prop sr1 sr2 lf_source lf_target;split => //.
move=> x y /=; rewrite  lf_source => xsf ysf.
rewrite (LfV tap xsf) (LfV tap ysf). 
split; move /Ninto_gleP => [pa pb pc]; apply/Ninto_gleP. 
  by split; try (apply: tap => //); apply: csum_Mleeq. 
split=> //; apply:(csum_le2l bN (Nint_S xsf) (Nint_S ysf)).
by rewrite csumC (csumC b y).
Qed.

Lemma card_Nintc a: natp a -> cardinal (Nintc a) = csucc a.
Proof. by move => aN; rewrite (NintcE aN) (card_card (CS_succ _)). Qed.

Lemma card_Nint a: natp a -> cardinal (Nint a) = a.
Proof. by move => aN; rewrite (NintE aN)(card_nat aN). Qed.

Lemma card_Nintcp a: natp a -> a <> \0c ->
  cardinal (Nintc (cpred a)) = a.
Proof.
move=> aN naz. 
by move: (cpred_pr aN  naz) => [fp ass]; rewrite card_Nintc.
Qed.

Theorem card_Nintcc a b: a <=N b -> 
  cardinal (Nintcc a b) = csucc (b -c a).
Proof. 
move=> [aN bN ab].
move: (cdiff_pr ab) (NS_diff a bN) => aux cN.
have fb:= (proj41 (restr_plus_interval_is cN aN)).
have eq: (Nintcc \0c (b -c a)) \Eq (Nintcc a b).
  exists (rest_plus_interval (b -c a) a); rewrite /rest_plus_interval.
  by hnf;rewrite lf_source lf_target; split => //; rewrite csumC aux.
by rewrite -(card_Nintc cN); symmetry;apply /card_eqP.
Qed.

  
Lemma card_Nint1c a: natp a -> cardinal (Nint1c a) = a.
Proof. 
move => aN.
case: (equal_or_not a \0c) => anz.
  have aux: (Nint1c \0c = emptyset).
    apply /set0_P => y; move /(Nint1cPb NS0)=> [c1y cy0].
    exact: (cleNgt (cleT c1y cy0) clt_01). 
  rewrite anz aux; apply: cardinal_set0.
have aux1: \1c <=c a by apply: cge1; fprops.
have aux: \1c <=N a by split;fprops.
have so:= (NS_diff \1c aN).
by rewrite card_Nintcc // Nsucc_rw // csumC; apply: cdiff_pr. 
Qed.

Lemma finite_Nintcc a b: finite_set (Nintcc a b).
Proof. 
apply/card_finite_setP. 
case: (p_or_not_p (a <=N b)) => h.
  rewrite card_Nintcc //; move: h => [aN bN _]; fprops.
have ->: (Nintcc a b) = emptyset.
  apply/set0_P => t /Zo_hi [/Nat_order_leP [pa _ pc] /Nat_order_leP [_ pe pf]].
  case: h; split => //; exact:cleT pc pf.
rewrite cardinal_set0;fprops.
Qed.

Lemma finite_Nint a: finite_set (Nint a).
Proof.
have aux:sub (Nint a) (Nintcc \0c a).
   by move => t /Zo_P [pa [pb [pc _]]]; apply /Zo_P.
apply: (sub_finite_set aux (finite_Nintcc \0c a)).
Qed.

Lemma infinite_Nat_alt: ~(finite_set Nat).
Proof. 
move /NatP =>h.
move: (sub_smaller (Nint_S (a:=\0c) (b:=cardinal Nat))).
by rewrite (card_Nintc h); case /(cleSltP h). 
Qed.

Lemma isomorphism_worder_finite r r': 
  total_order r -> total_order r' ->
  finite_set (substrate r) -> (substrate r) \Eq (substrate r') ->
  exists! f, order_isomorphism f r r'.
Proof. 
move=> tor tor' fs /card_eqP => sc.
have fs': finite_set (substrate r') by hnf; rewrite - sc.
move:(finite_set_torder_wor tor fs) (finite_set_torder_wor tor' fs'). 
have aux: forall u v f, order_isomorphism f u v  ->
   segmentp v (Imf f) /\ order_morphism f u v.
  move => f u v h; split; last by apply:order_isomorphism_w.
  move: h => [_ or' [[injf sjf] sf tf] pf].
  by rewrite (surjective_pr0 sjf) tf;  apply: substrate_segment.
move => wor wor'; case: (isomorphism_worder_exists wor wor').
  move => [f [pa mf]]; exists f; split.
    move: (order_morphism_fi mf) => injf.
    move: mf => [o1 o2 [ff sf tf] pf]; split => //; split => //. 
    by apply: bijective_if_same_finite_c_inj; [ by rewrite sf tf | ue| exact].
  by move => f'/aux [qa qb]; apply:(isomorphism_worder_unique wor wor').
move => [f [pa mf]]. 
have oi: (order_isomorphism f r' r).
  move: (order_morphism_fi mf) => injf.
  move: mf => [o1 o2 [ff sf tf] pf].
   have bf: bijection f by apply: bijective_if_same_finite_c_inj;
     rewrite ? sf ?tf;[ symmetry; apply: sc|  exact| exact].
   split=> //.
move: (inverse_order_is oi)=> oii.
exists (inverse_fun f); split => //  f' h1.
move: (aux _ _ _ (inverse_order_is h1)) => [sa sb].
move: h1 => [_ _ [[[ff _] _] _ _] _ ].
by rewrite(isomorphism_worder_unique wor' wor pa sa mf sb)(ifun_involutive ff).
Qed.

Theorem finite_ordered_interval r: total_order r ->
  finite_set (substrate r) -> 
  exists! f, order_isomorphism f r 
    (Nint_cco \1c (cardinal (substrate r))).
Proof.
move=> tot fs.
move/NatP: (fs) => fs'.
have [pa pb] := (Ninto_wor \1c (cardinal (substrate r))).
move /card_eqP:(card_Nint1c fs') ;rewrite /Nint1c - pb => /EqS h.
by apply: (isomorphism_worder_finite tot (worder_total pa) fs).
Qed.

Theorem finite_ordered_interval1 r: total_order r ->
  finite_set (substrate r) -> 
  exists !f, order_isomorphism f r 
    (Nint_co (cardinal (substrate r))).
Proof.
move=> tor fs.  
move/NatP: (fs) =>  fs'.
have wor := (finite_set_torder_wor tor fs).
move /card_eqP:(card_Nint fs'); rewrite - (proj2 (Nintco_wor _)) => /EqS e. 
have tor' := (worder_total (proj1(Nintco_wor (cardinal (substrate r))))).
by apply: (isomorphism_worder_finite tor tor' fs).
Qed.


Lemma finite_ordered_interval2 r: total_order r ->
  finite_set (substrate r) -> 
  r \Is  (Nint_co (cardinal (substrate r))).
Proof.
move => ha hb; have [f [isf _]] :=(finite_ordered_interval1 ha hb).
by exists f.
Qed.

(* this uses the method of Exercise 4.3 *)

Lemma worder_decreasing_finite r r' (f:fterm):
  worder r -> worder r' ->
  (forall i, inc i (substrate r) -> inc (f i) (substrate r')) ->
  (forall i j, glt r i j -> glt r' (f j) (f i)) ->
  finite_set (substrate r).
Proof.
move => wo1 wo2 hyp1 hyp2.
case: (emptyset_dichot (substrate r)) => Ene.
   rewrite Ene; apply: emptyset_finite.
set A := Zo (substrate r) (fun z => finite_set (segment r z)).
have neZ: nonempty A.
  move:(worder_least wo1 Ene) =>[x [xsr xle]]; exists x; apply: (Zo_i xsr).
  suff: (segment r x) = emptyset by move ->; apply: emptyset_finite.
  apply /set0_P => y /segmentP ys.
  have ysr: inc y (substrate r) by order_tac.
  move: (xle _ ysr) (proj1 wo1) => le1 or; order_tac.
set B := fun_image A f.
have sB: sub B (substrate r') by move => t /funI_P[x /Zo_S /hyp1 h ->].
have neB: nonempty B by apply: funI_setne.
move: (worder_prop wo2 sB neB) =>[b /funI_P [a /Zo_P [asr sf] av] bp].
have o1 := proj1 wo1.
move: (segmentc_pr o1 asr) (segmentc_segment a o1) => eq1 us.
have fs2: finite_set  (segmentc r a) by rewrite - eq1; apply: setU1_finite.
case: (well_ordered_segment  wo1 us); first by move <-.
move => [c csr cv]. 
have cA: inc c A by  apply: (Zo_i csr); rewrite - cv.
have cB: inc (f c) B by  apply: funI_i.
move: (bp _ cB). rewrite av => / (not_le_gt (proj1 wo2)); case.
apply: hyp2. apply/segmentP; rewrite - cv; fprops.
Qed.


  
  
(** A finite sum or product can be defined by induction *)

Lemma induction_on_sum n f (sum := fun n => csumb n f):
  natp n -> sum (csucc n) = (sum n) +c (f n).
Proof. 
move=> nN; rewrite /sum (succ_of_nat nN); apply csumA_setU1.
apply:(Nat_decent nN).
Qed.

Lemma induction_on_prod n f (prod := fun n=> cprodb n f): 
  natp n -> prod (csucc n) = (prod n) *c (f n).
Proof. 
move=> nN; rewrite /prod (succ_of_nat nN); apply cprodA_setU1.
apply:(Nat_decent nN).
Qed.

Lemma fct_sum_rec0 f n: natp n ->
  csumb (Nintc n) f = (csumb (Nint1c n) f) +c (f \0c).
Proof.
move=> nN; move: (Nint_pr5 nN) => [<- aux].
by apply csumA_setU1.
Qed.

Lemma fct_sum_rec1 f n: natp n ->
  csumb (csucc n) f = (csumb n (fun i=> f (csucc i))) +c (f \0c).
Proof.
move=> nN.
rewrite - (NintE (NS_succ nN)) -(Nint_co_cc nN).
rewrite (fct_sum_rec0 _ nN); congr (_ +c  (f \0c)).
have aux u: inc u n -> cardinalp u.
   move =>h; exact:(CS_nat (NS_inc_nat nN h)).
apply: csum_Cn2; split.
+ move => t /(NltP nN) => tn; apply /(Nint1cP nN).
  by split; [ apply: succ_nz |  apply/(cleSltP (NS_lt_nat tn nN))]. 
+ by move=> u v un vn;apply: csucc_inj; apply: aux.
+ move=> y; aw; move/(Nint1cP nN) => [nyz le_s].
  have  [pN ns] := (cpred_pr (NS_le_nat le_s nN) nyz).
  exists (cpred y) => //; apply/(NltP nN); apply/(cleSltP pN); ue.
Qed.

Lemma fct_sum_rev f n (I := (csucc n)): 
  natp n -> csumb I f = csumb I (fun i=> f (n -c i)).
Proof.
move=> nN.
have snN:= NS_succ nN.
apply: csum_Cn2; split.  
+ by move=> x /(NleP nN) [_ cn _];apply /(NleP nN); apply: cdiff_ab_le_a. 
+ move=> x y /(NleP nN) xn  /(NleP nN) yn => h.
  by rewrite - (double_diff nN xn) -(double_diff nN yn) h.
+ aw => y /(NleP nN) yn;  rewrite -(double_diff nN yn).
  exists (n -c y) => //; apply /(NleP nN).
  exact: (cdiff_ab_le_a _ (proj32 yn)).
Qed.

(** ** EIII-5-4 Finite sequences *)


(** ** EIII-5-5 Characteristic functions on sets *)

Lemma char_fun_V_aa A x: inc x A ->
  Vf (char_fun A A) x = \1c.
Proof. by move => xa; rewrite char_fun_V_a. Qed.

Lemma char_fun_V_bb A x:  inc x A ->
  Vf (char_fun emptyset A) x = \0c.
Proof.  
move => xa; rewrite char_fun_V_b ? setC_0;fprops. 
Qed.

Lemma char_fun_constant A B:
   sub A B -> (cstfp (char_fun A B) B) -> (A=B \/ A = emptyset).
Proof.
move=> AB p.
case: (emptyset_dichot A); [by right | move=> [u uA]; left ].
apply: extensionality=>// t tB.
ex_middle v;case: card1_nz.
move: (p u t (AB _ uA) tB). rewrite (char_fun_V_a AB uA) (char_fun_V_b AB) //.
by apply /setC_P.
Qed.

Lemma char_fun_setC A B x: sub A B -> inc x B ->
  Vf (char_fun (B -s A) B) x = \1c -c (Vf (char_fun A B) x).
Proof. 
move=> AB xB.
have sc:= (@sub_setC B A).
case: (inc_or_not x A) => xA.
  rewrite char_fun_V_b ? setC_K //.
  by rewrite char_fun_V_a // (cdiff_nn).
move/setC_P: (conj xB xA) => xc.
by rewrite char_fun_V_a // char_fun_V_b // (cdiff_n0 NS1).
Qed.

Lemma char_fun_setI A A' B x: sub A B -> sub A' B -> inc x B ->
  Vf (char_fun (A \cap A') B) x 
  =  (Vf (char_fun A B) x)  *c (Vf (char_fun A' B) x).
Proof. 
move=>  AB A'B xB.
have Ha:sub (A \cap A') B by move=> t /setI2_P [tA _]; apply: AB.
case: (inc_or_not x A) => h. 
  have cW:cardinalp (Vf (char_fun A' B) x) by apply: char_fun_V_cardinal.
  rewrite (char_fun_V_a AB h) cprod1l //. 
  case: (inc_or_not x A') => xA.
    have aux:inc x (A \cap A') by apply: setI2_i.
    rewrite char_fun_V_a // char_fun_V_a //.
  have aux:inc x (B -s (A \cap A')) 
    by apply /setC_P;split => //; move /setI2_P =>[_].
  by rewrite char_fun_V_b // char_fun_V_b //; apply /setC_P.
have aux: inc x (B -s (A \cap A'))
 by apply /setC_P;split => //; move /setI2_P =>[].
have aux2:inc x (B -s A) by fprops.
by rewrite char_fun_V_b // char_fun_V_b // cprod0l.
Qed.

Lemma char_fun_setU A A' B x: sub A B -> sub A' B -> inc x B ->
  (Vf (char_fun (A \cap A') B) x)
  +c (Vf (char_fun (A \cup A') B) x)
  =  (Vf (char_fun A B) x) +c (Vf (char_fun A' B) x).
Proof. 
move=> AB A'B xB.
have Ha:sub (A \cap A') B by move=> t /setI2_P [ta _]; apply: AB.
have Hb:sub (A \cup A') B by move=> t /setU2_P; case; fprops.
case: (p_or_not_p (inc x A))=> xA.
  rewrite (char_fun_V_a AB xA).
  rewrite (char_fun_V_a Hb (setU2_1 A' xA)).
  case: (p_or_not_p (inc x A'))=> xA'. 
    by rewrite (char_fun_V_a A'B xA') char_fun_V_a //; apply: setI2_i.  
  rewrite csumC; apply: f_equal. 
  by rewrite ! char_fun_V_b //; apply /setC_P; split => //; move /setI2_P => [].
have Hc: inc x (B -s A) by fprops.
have Hd:inc x (B -s (A \cap A')).
  by apply /setC_P; split => //; move /setI2_P => [].
rewrite  (char_fun_V_b AB Hc) (char_fun_V_b Ha Hd). 
case: (p_or_not_p (inc x A')) => aux.
  have xu: inc x (A \cup A') by  apply: setU2_2.
  by rewrite (char_fun_V_a Hb xu) (char_fun_V_a A'B aux). 
have xc:inc x (B -s (A \cup A')).
  by apply /setC_P; split => //;move /setU2_P => [].
have xba: inc x (B -s A')  by fprops.
by rewrite (char_fun_V_b Hb xc) (char_fun_V_b A'B xba).  
Qed.

(** ** EIII-5-6 Euclidean Division *)


Definition cdivision_prop a b q r := 
  a = (b *c q) +c r /\ r <c b.

Lemma cdivision_prop_alt a b q r: natp a -> natp b ->
  natp q -> natp r -> b <> \0c ->
  (cdivision_prop a b q r <->
  [/\ (b *c q) <=c a, a <c (b *c csucc q) & r =  a -c (b *c q)]).
Proof. 
move=> aN bN qN rN nzb; rewrite /cdivision_prop.
set (w:= b *c q).
rewrite Nsucc_rw // cprodC cprodDl cprodC cprod1l; fprops.
have wN: natp w by rewrite /w; fprops.
split.
  move=> [av lt];split => //.
  - by rewrite av; apply: Nsum_M0le.
  - rewrite av; apply: csum_Mlelt; fprops.
  - by symmetry;apply: cdiff_pr2 =>//; symmetry; rewrite csumC.
move=> [lwa ltas rv].
rewrite rv.
have aux: natp (b *c q +c b) by fprops.
split; first by symmetry; apply: cdiff_pr =>//. 
move: ltas => /(card_ltP aN aux) [c [cN nzc s]] {aux}.
move: (cdiff_pr lwa); rewrite -rv=> aux.
apply /(card_ltP rN bN); exists c => //; split => //.
by apply: (csum_eq2l wN (NS_sum rN cN) bN);rewrite csumA  aux.
Qed.

Lemma cdivision_unique a b q r q' r': natp a -> natp b ->
  natp q -> natp r -> natp q' -> natp r'  -> b <> \0c ->
  cdivision_prop a b q r -> cdivision_prop a b q' r' ->
  (q = q' /\ r =r').
Proof.
move=> aN bN qN rN q'N r'N nbz.
move /(cdivision_prop_alt aN bN qN rN nbz)=> [le1 lt1 e1].  
move /(cdivision_prop_alt aN bN q'N r'N nbz)=> [le2 lt2 e2].  
suff : q = q' by move=> h; split => //; rewrite e1 e2 h.
move: (cprod_lt2l bN q'N (NS_succ qN) (cle_ltT le2 lt1)).
move: (cprod_lt2l bN qN (NS_succ q'N) (cle_ltT le1 lt2)).
by move /(cltSleP q'N) => pa /(cltSleP qN) => /(cleA pa).
Qed.


Definition cquo_internal a b := 
  least_ordinal (fun q => a <c b *c csucc q) a.
Definition cquo := locked cquo_internal.
Definition crem_internal a b := a -c (b *c (cquo a b)).
Definition crem := locked crem_internal. 

Definition cdivides b a := 
  [/\ natp a, natp b & crem a b = \0c].

Notation "x %/c y" := (cquo x y) (at level 40).
Notation "x %%c y" := (crem x y) (at level 40).
Notation "x %|c y" := (cdivides x y) (at level 40).

Lemma cquoE x y: x %/c y = cquo_internal x y.
Proof.  by rewrite /cquo - lock. Qed.
Lemma cremE x y: x %%c y = crem_internal x y.
Proof.  by rewrite /crem - lock. Qed.


Lemma cdivision a b (q := a %/c b) (r :=  a %%c b):
  natp a -> natp b -> b <> \0c ->
  [/\ natp q, natp r & cdivision_prop a b q r].
Proof.
move=> aN bN bnz. 
pose pr z := (a <c b *c (csucc z)).
have pa: pr a by apply /(cleSltP aN);rewrite cprodC; apply: Nprod_M1le; fprops.
case: (least_int_prop aN pa).
rewrite /pr - /(cquo_internal _ _) - cquoE.
move => qN qa qb. 
have rv: r = a -c b *c q by rewrite/r cremE.
have rN: natp r by rewrite rv; apply: NS_diff => //; apply: NS_prod.
split => //.
apply /cdivision_prop_alt=> //; split => //.
case: (equal_or_not q \0c); first by move -> ; rewrite cprod0r; apply: cle0n.
move => qz; move: (cpred_pr qN qz) =>[sa sb].
case: (NleT_el (NS_prod bN qN) aN) => //; rewrite {1} sb => W.
by case: (cleNgt(qb _ sa W)); rewrite{2} sb; apply: cltS.
Qed.

Lemma cquo_zero a: a %/c \0c = \0c.
Proof.
rewrite cquoE /cquo_internal /least_ordinal; set E := Zo _ _.
have -> : E = emptyset.
  apply /set0_P => y /Zo_hi; rewrite cprod0l; apply: clt0.
by rewrite setI_0.
Qed.

Lemma crem_zero a: natp a -> a %%c \0c = a.
Proof. by move => h; rewrite cremE /crem_internal cprod0l cdiff_n0. Qed.

Lemma NS_quo a b: natp a -> natp (a %/c b).
Proof. 
rewrite cquoE /cquo_internal /least_ordinal => /olt_omegaP aN.
set E := Zo _ _.
have nsE x: inc x E -> natp x.
  move => /Zo_S /(oleP (proj31_1 aN)) xa; apply/olt_omegaP; apply: (ole_ltT xa aN).
have osE: ordinal_set E by move => t /nsE /OS_nat. 
case: (emptyset_dichot E) => Enz; first by rewrite Enz setI_0; fprops.
exact: (nsE _ (ordinal_setI Enz osE)).
Qed.

Lemma NS_rem a b: natp a -> natp (a %%c b).
Proof. 
move => aN ; rewrite cremE; apply: (NS_diff _ aN).
Qed.

Hint Resolve  NS_rem NS_quo: fprops.

Lemma cdiv_pr a b: natp a -> natp b -> 
  a = (b *c (a %/c b)) +c (a %%c b).
Proof.
move => aN bN.
case: (equal_or_not b \0c) => bnz.
  by rewrite bnz (crem_zero aN) cquo_zero cprod0r Nsum0l.
by move: (cdivision aN bN bnz) =>[_ _ [h _]].  
Qed.

Lemma crem_pr a b: natp a -> natp b -> b <> \0c ->
  (a %%c b) <c b.
Proof.
by move => aN bN bnz; move: (cdivision aN bN bnz) =>[_ _ [_]].  
Qed.

Lemma cquorem_pr a b q r:
  natp a -> natp b -> natp q -> natp r ->
  cdivision_prop a b q r -> (q = a %/c b /\ r = a %%c b).
Proof.
move => aN bN qN rN p'.
case: (equal_or_not b \0c) => bnz.
  move: p' => [_ ]; rewrite bnz =>h; case: (clt0 h).
move: (cdivision aN bN bnz)=> [qqN rrN p].
apply: (cdivision_unique aN bN qN rN qqN rrN bnz p' p).
Qed.

Lemma cquorem_pr0 a b q: 
  natp a -> natp b -> natp q -> b <> \0c ->
   a = (b *c q) -> (q = a %/c b /\ \0c = a %%c b).
Proof.
move => aN bN qN bnz p'.
apply: cquorem_pr; fprops.
hnf; rewrite -p' (Nsum0r aN).  
split;  [ trivial | split; [  apply: cle0x |  ]]; fprops.
Qed.

Lemma crem_small a b: natp b -> a <c b -> a = a %%c b.
Proof.
move => bN lab.
have aN:= (NS_lt_nat lab bN).
have h:cdivision_prop a b \0c a; first by split => //; rewrite cprod0r Nsum0l.
exact: (proj2 (cquorem_pr aN bN NS0 aN h)).
Qed.

Lemma cquo_small a b: natp b -> a <c b -> a %/c b = \0c.
Proof.
move => bN lab.
have aN:=(NS_lt_nat lab bN).
have h: cdivision_prop a b \0c a. 
  by split => //; rewrite cprod0r (csum0l (CS_nat aN)).
symmetry; exact:(proj1 (cquorem_pr aN bN NS0 aN h)).
Qed.

Lemma cdivides_pr a b: 
  b %|c a -> a =  b *c (a %/c b).
Proof. 
move => [aN bN dv].
move: (cdiv_pr aN bN); rewrite dv.
by rewrite (Nsum0r (NS_prod bN (NS_quo b aN))). 
Qed.

Lemma cdivides_pr1 a b: natp a -> natp b -> b %|c (b *c a).
Proof. 
move=> aN bN.
move: (NS_prod bN aN) => pN.
split => //.
case: (equal_or_not b \0c) => bnz.
  rewrite bnz cprod0l crem_zero //; fprops.
by case: (cquorem_pr0 pN bN aN bnz (refl_equal (b *c a))).
Qed.

Lemma cdivides_pr2 a b q: 
  natp a -> natp b -> natp q -> b <> \0c ->
  a = b *c q -> q = a %/c b.
Proof. 
move => aN bN qN nzb abq.
by case: (cquorem_pr0 aN bN qN nzb abq).
Qed. 

Lemma cdivides_one a: natp a ->  \1c %|c  a.
Proof. 
move=> aN; rewrite - (cprod1l (CS_nat aN)).
apply: (cdivides_pr1 aN NS1).
Qed.

Lemma cquo_one a: natp a -> a %/c \1c = a.
Proof.
move=> aN; symmetry; apply: cdivides_pr2; fprops.
rewrite cprod1l;fprops.
Qed.

Lemma cdivides_pr4 b q: natp b -> natp q -> b <> \0c ->
   (b *c q) %/c b = q.
Proof. move=> bN qN bnz; symmetry; apply: cdivides_pr2;  fprops. Qed.

Lemma cdivision_of_zero n:  natp n -> 
  (n %|c \0c /\ \0c %/c n = \0c).
Proof. 
move: NS0 => n0 aN; rewrite /cdivides. 
have aux: \0c = n *c \0c by rewrite cprod0r.  
case: (equal_or_not n \0c) => anz.
  by rewrite  anz cquo_zero crem_zero. 
by move: (cquorem_pr0 n0 aN n0 anz aux) => [p1 p2]. 
Qed.

Lemma cdivides_zero n: natp n -> n %|c \0c.
Proof. by move/cdivision_of_zero => []. Qed.

Lemma crem_of_zero n: natp n -> \0c %%c n = \0c.
Proof. by move /cdivides_zero => []. Qed.

Lemma cdivision_itself a: natp a -> a <> \0c ->
  (a %|c a /\ a %/c a = \1c).
Proof.
move=> aN anz; rewrite /cdivides. 
have aux:= esym (cprod1r (CS_nat aN)).
by move: (cquorem_pr0 aN aN NS1 anz aux) => [p1 p2]. 
Qed.

Lemma cdivides_itself n: natp n -> n %|c n.
Proof. 
move=> aN; case: (equal_or_not n \0c) => nz.
  by rewrite {2} nz; apply:cdivides_zero.
exact:(proj1 (cdivision_itself aN nz)). 
Qed.

Lemma cquo_itself a: natp a -> a <> \0c ->
   a %/c a = \1c.
Proof. by move=> aN anz; move: (cdivision_itself aN anz) => [ _ h]. Qed.

Lemma cdivides_trans a b a':
  a  %|c a'-> b  %|c a  ->  b  %|c a'.
Proof. 
move=> d1 d2.
rewrite (cdivides_pr d1) {1} (cdivides_pr  d2) - cprodA.
move: d1 d2 => [p1 p2 _] [p3 p4 _].
apply: cdivides_pr1 =>//; fprops.
Qed.

Lemma cdivides_trans1 a b a':
  a  %|c a' -> b %|c a -> a'  %/c b = (a' %/c a) *c (a  %/c b).
Proof.
move=> d1 d2.
move: (cdivides_pr d1).  
rewrite {1} (cdivides_pr d2) - cprodA => h.
case: (equal_or_not b \0c) => bnz.
  by rewrite bnz cquo_zero cquo_zero cprod0r. 
move: d1 d2 => [a'N aN _][_ bN _].
have pN: natp ((a %/c b) *c (a' %/c a)) by fprops.
rewrite - (cdivides_pr2 a'N bN pN bnz h).   
by rewrite cprodC. 
Qed.

Lemma cdivides_trans2 a b c: natp c ->
  b %|c a -> b  %|c (a *c c).
Proof. 
move=> cN ba.
have aN: (inc a Nat) by move: ba => [h _].
have aux:= (cdivides_pr1 cN aN).
apply: (cdivides_trans aux ba).  
Qed.

Lemma cdivides_smaller a b: b %|c a -> a <> \0c -> b <=c a.
Proof.
move => ha.
rewrite (cdivides_pr ha) => hb.
case: (equal_or_not (a %/c b) \0c) => qz.
  by case: hb; rewrite qz cprod0r.
apply: (cprod_M1le (CS_nat (proj32 ha)) qz).
Qed.


Lemma cdivides_order : order_r cdivides.
Proof.
split.
- by move => u v w ha hb; apply: (cdivides_trans hb ha).
- move=> u v ha hb.
  case: (equal_or_not u \0c) => uz.
    by move: (cdivides_pr ha); rewrite uz cprod0l.
  case: (equal_or_not v \0c) => vz.
    by move: (cdivides_pr hb); rewrite vz cprod0l.
  apply: cleA.
    exact:(cdivides_smaller ha vz). 
    exact:(cdivides_smaller hb uz). 
- by move => u v [vN uN _]; split; apply: cdivides_itself.
Qed.

  

Lemma cquo_simplify a b c:
  natp a -> natp b -> natp c -> b <> \0c -> c <> \0c ->
  (a *c c) %/c (b *c c) =  a %/c b.
Proof. 
move=> aN bN cN bnz cnz.
have [qN rN []] := (cdivision aN bN bnz).
set q:=  (a %/c b); set r := a %%c b.
move=> e1 lrb; symmetry.
move: (NS_prod aN cN)(NS_prod bN cN)(NS_prod (NS_rem b aN) cN)  => p1 p2 p3.
have dv: (cdivision_prop  (a *c c) (b *c c) q (r *c c)).
  split. 
     rewrite (cprodC b c) - cprodA (cprodC c _).
    by rewrite - cprodDl e1.
  by rewrite (cprodC b c) cprodC; apply: cprod_Meqlt.
exact (proj1 (cquorem_pr p1 p2 qN p3 dv)).
Qed.

Lemma cdivides_sum a a' b:  b %|c a ->  b %|c a' ->
    (b %|c  (a +c a') /\ 
    (a +c a') %/c b = (a %/c b) +c (a' %/c b)).
Proof. 
move=> d1 d2.
move: (cdivides_pr d1)(cdivides_pr d2)=> am bm.
set s := (a %/c b) +c (a' %/c b).
have ->: (a +c a' = b *c s) by rewrite /s cprodDr -am -bm.
move: d1 d2 => [aN bN _][a'N _ _].
have sN:natp s by rewrite /s; fprops.
split; first by apply: cdivides_pr1 =>//. 
case: (equal_or_not b \0c) => bs.
  rewrite {2} /s bs ! cquo_zero csum0l; fprops.
by symmetry; apply: (cdivides_pr2 (NS_prod bN sN) bN sN bs). 
Qed.


Lemma cdivides_diff a a' b:
  a' <=c a ->   b %|c a ->  b %|c a' ->
  [/\ b %|c  (a -c a'), (a' %/c b) <=c (a %/c b) &
    (a -c a') %/c b = (a %/c b) -c (a' %/c b)].
Proof.
move=> le d1 d2.
move: (cdivides_pr d1)(cdivides_pr d2)=> am bm.
set s :=  (a %/c b) -c (a' %/c b).
move: d1 d2 => [aN bN _][a'N _ _].
move: (NS_quo b aN)(NS_quo b a'N) => q1 q2.
have q3: (a' %/c b) <=c (a %/c b).
  case: (equal_or_not b \0c) => bnz.
    rewrite bnz ! cquo_zero; fprops.
  rewrite am bm in le; apply: (cprod_le2l bN q2 q1 bnz le).
have ->: (a -c a' = b *c s).
  by rewrite /s cprodBl // -am -bm.
have sN: natp s by rewrite /s; fprops.
split => //; first by apply: cdivides_pr1 =>//. 
case: (equal_or_not b \0c) => bs.
  rewrite {2} /s bs ! cquo_zero cdiff_nn; fprops. 
by symmetry; apply: (cdivides_pr2 (NS_prod bN sN) bN sN bs). 
Qed.


Lemma cdivides_diff1 x a b: natp b -> x %|c a ->  x %|c (a +c b) -> x %|c b.
Proof.
move => bN ha hb.
move:(ha) => [aN xN _].
move:(Nsum_M0le b aN) => le1.
by move:(proj31 (cdivides_diff le1 hb ha)); rewrite csumC cdiff_pr1.
Qed.


(** ** EIII-5-7 Expansion to base b *)


(** Definition by induction on N *)


Definition induction_defined0 (h: fterm2)  (a: Set) :=
  transfinite_defined Nat_order 
  (fun u => variant \0c a 
     (h (cpred (source u))(Vf u (cpred (source u)))) (source u)).
Definition induction_defined (s: fterm)  (a: Set) :=
  induction_defined0 (fun u v => s v) a.

Lemma induction_defined_pr0 (h:fterm2) a (f :=  induction_defined0 h a):
     [/\ source f = Nat,  surjection f, Vf f \0c = a &
     forall n, natp n -> Vf f (csucc n) = h n (Vf f n)].
Proof.
rewrite /f /induction_defined0.
set p :=  (fun u : Set => _).
have [wo sr] := Nat_order_wor.
move: (transfinite_defined_pr p wo) => [].
set g := (transfinite_defined Nat_order p) => pa pb pc.
have p1: forall a, natp a -> 
   source (restriction1 f (segment Nat_order a))= a.
  by move=> b bN; rewrite /restriction1 corresp_s segment_Nat_order1. 
rewrite sr in pb pc; split => //.
  by rewrite (pc _ NS0) /p (p1 _ NS0) variant_true0. 
move=> n nN;  move:(NS_succ nN) => snN;rewrite (pc _ snN) /p  (p1 _ snN).
rewrite (variant_false _ _ (@succ_nz n)) (cpred_pr2 nN).
congr (h n _); rewrite restriction1_V //; first by fct_tac. 
  rewrite segment_Nat_order // ? pb;apply: Nint_S1. 
by rewrite (segment_Nat_order snN); apply: Nint_si.
Qed.

Lemma induction_defined_pr s a (f :=  induction_defined s a):
    [/\ source f = Nat,  surjection f, Vf f \0c  = a &
     forall n, natp n -> Vf f (csucc n) = s (Vf f n)].
Proof.
exact: (induction_defined_pr0 (fun u v => s v) a).
Qed.


Lemma integer_induction0 h a: exists! f,
  [/\ source f = Nat, surjection f,
    Vf f \0c = a &
    forall n, natp n -> Vf f (csucc n) = h n (Vf f n)].
Proof. 
exists (induction_defined0 h a); split.
  apply: (induction_defined_pr0).
move:(induction_defined_pr0 h a) => [sy sjy y0 ys] x [sx sjx x0 xs].
apply: function_exten4=>//; first by ue.
rewrite sy; apply: Nat_induction; first by ue.
by move=> n nN eq; rewrite  (xs _ nN) (ys _ nN) eq.
Qed.

Lemma integer_induction (s:fterm) a: exists! f,
  [/\ source f = Nat,  surjection f, Vf f \0c = a &
  forall n, natp n -> Vf f (csucc n) = s (Vf f n)].
Proof. 
move: (integer_induction0 (fun _ x:Set => s x) a) => //. 
Qed.

Definition induction_term s a := Vf (induction_defined0 s a).

Lemma induction_term0 (s:fterm2) a:
  induction_term s a \0c = a.
Proof.
by move: (induction_defined_pr0 s a)=> [sf sjf w0 ws].
Qed.

Lemma induction_terms s a n:
  natp n ->
  induction_term s a (csucc n) = s n (induction_term s a n).
Proof.
move: (induction_defined_pr0 s a)=> [sf sjf w0 ws] nN.
by rewrite /induction_term ws.
Qed.

(** Expansion to base b *)



Lemma b_power_k_large a b: natp a -> natp b ->
  \1c <c b -> a <> \0c -> exists k,
    [/\ natp k, (b ^c k) <=c a & a <c (b ^c (csucc k))].
Proof. 
move=> aN bN l1b naz.
pose prop  x :=  a <c (b ^c x).
have exp: prop a by  apply: cpow_M1lt;fprops.
case: (least_int_prop2 aN exp).
  rewrite /prop cpowx0 => a1; case(cltNge a1 (cge1 (CS_nat aN) naz)).
set k := cpred _; move => [kN pks npk].
exists k; split => //.
by case: (NleT_el (NS_pow bN kN) aN) => // h; case: npk.
Qed.

Definition expansion f b k :=
  [/\ natp b, natp k, \1c <c b &
  [/\ fgraph f, domain f = k &
  forall i, inc i (domain f) -> (Vg f i) <c b]].

Definition expansion_value f b :=
  csumb (domain f) (fun i=> (Vg f i) *c (b ^c i)).

Section Base_b_expansion.
Variables f g b k k': Set.
Hypothesis Exp: expansion f b k.
Hypothesis Expg: expansion g b (csucc k').
Hypothesis ck' : cardinalp k'.
 
Lemma expansion_prop0P i:
   (inc i (domain f)) <-> i <c k.
Proof. have [_ kn _  [_ -> _]] := Exp; apply: iff_sym ;exact: (NltP kn). Qed.

Lemma expansion_prop1 i:
  i <c k -> natp (Vg f i).
Proof. 
move: Exp => [bN kn _ [_ d v]] /expansion_prop0P /v lt1.
exact:(NS_lt_nat lt1 bN).
Qed.

Lemma expansion_prop2:
   finite_int_fam  (Lg (domain f) (fun i=> (Vg f i) *c  (b ^c i))).
Proof. 
have [bN kN b2 [fgf df vf]] := Exp.
hnf; rewrite /allf; aw; split.
  move=> i idf; rewrite LgV//; move /expansion_prop0P: idf  => idf.
  apply: (NS_prod (expansion_prop1 idf) (NS_pow bN (NS_lt_nat idf kN))).
by rewrite df; apply: finite_set_nat.
Qed.

Lemma expansion_prop3: natp (expansion_value f b).
Proof. 
rewrite /expansion_value; apply: finite_sum_finite. 
apply: expansion_prop2.
Qed.

Lemma expansion_prop4: natp k'.
Proof. by move: Expg => [_ kN' _ _]; apply: NS_nsucc. Qed.

Lemma expansion_prop5: 
  expansion (restr g  k') b k'.
Proof. 
have k'n :=expansion_prop4.
have [bN kN b2 [fgf df vf]] := Expg.
have dr: domain (restr g k') = k' by  aw.
split;fprops; split; fprops.
by rewrite dr=> i ic; rewrite LgV//; apply: vf; rewrite df; apply: (proj33(cleS k'n)).
Qed.

Lemma expansion_prop6: natp (Vg g k').
Proof. 
have k'n := expansion_prop4.
have [bN kn _ [_ d v]] := Expg.
have kd: (inc k' (domain g)) by  rewrite d; apply/(NleP k'n); fprops.
exact:(NS_lt_nat (v _ kd) bN). 
Qed.

Lemma expansion_prop7: 
  (expansion_value g b) = 
   (expansion_value (restr g k') b) +c (Vg g k' *c (b ^c k')).
Proof. 
have k'n:= (expansion_prop4).
pose h i := (Vg g i) *c (b ^c i).
have ->: (Vg g k') *c (b ^c  k') = h k' by [].
move: (induction_on_sum h k'n).
have <- : domain g = (csucc k') by move: Expg=> [_ _ _ [_ dg _]].
rewrite /expansion_value /restr Lgd  => ->.
by congr ( _ +c (h k')); apply:csumb_exten => x xi; rewrite LgV.
Qed.

End  Base_b_expansion.

Lemma expansion_prop8 f b k x
    (h:=  Lg (csucc k) (fun i=> variant k x (Vg f i) i)) :
   expansion f b k -> natp x -> x <c b -> 
    (expansion h b (csucc k) /\
      expansion_value h  b = 
      (expansion_value f b) +c ((b ^c k)  *c x)).
Proof. 
move=> [bN kN b2 [fgf df vf]] xN xb.
have eg: (expansion h b (csucc k)). 
  hnf; rewrite /h; aw;split;fprops; split; fprops.
  move=> i idh; rewrite LgV//; move /(NleP kN): idh; case/cle_eqVlt.
   by move ->; rewrite variant_true0.
  move=> lik; rewrite (variant_false _ _  (proj2 lik)); apply: vf.
  by rewrite df; apply/NltP.
have ck: cardinalp k by fprops.
have ksk := (proj33 (cleS kN)).
rewrite (expansion_prop7 eg ck); split; first by exact.
have ->:(restr h k = f).
  rewrite /h; symmetry;apply: fgraph_exten; [ exact | fprops | aww | ].
  rewrite df; move=> y ydf /=; rewrite !LgV//; fprops; rewrite variant_false //.
  by move/(NltP kN)/proj2: ydf.
have -> //: (Vg h k *c (b ^c  k)  = (b ^c k) *c x).
by rewrite cprodC /h LgV//;[ rewrite variant_true0 | apply: (Nsucc_i kN)].
Qed.

Lemma expansion_prop8_rev f b k x
  (h := Lg (csucc k) (fun i => variant \0c x (Vg f (cpred i)) i )):
  expansion f b k -> natp x -> x <c b -> 
  (expansion h b (csucc k) /\
      expansion_value h b =  (expansion_value f b) *c b  +c x).
Proof.
move => [bN kN b2 [fgf df vf]] xN xs. 
have skN:= (NS_succ kN).
split.
  hnf;rewrite /h;split => //; aw; split; fprops => i ii; rewrite LgV//. 
  rewrite /variant;Ytac iz => //.
  move/(NleP kN):ii => lij; move:(cpred_pr (NS_le_nat lij kN) iz) => [sa sb].
  apply: vf; rewrite df; apply/(NltP kN);apply /(cleSltP sa); ue.
move /(NleP kN): (cle0n kN) => zi.
have ha:= (CS_nat xN).
have hb: (Vg h \0c *c b ^c \0c) = x. 
   by rewrite /h LgV //; aw; rewrite cpowx0 (cprod1r ha).
rewrite /expansion_value df {1} /h Lgd (fct_sum_rec1 _ kN) hb //.
congr (_ +c x).
move: (kN) (cleR (CS_nat kN)); move: {- 3} k; apply: Nat_induction.
  move => _; rewrite /csumb !csum_trivial; aw; trivial.
  by rewrite cprod0l.
move => n nN Hrec sa.
have hc: inc (csucc n) (csucc k) by apply /(NleP kN).
rewrite (induction_on_sum _ nN) (induction_on_sum _ nN).
rewrite (Hrec (cleT (cleS nN) sa)) cprodDl - cprodA  /h (LgV hc).
by rewrite (variant_false _ _ (@succ_nz n))  (cpred_pr2 nN) (cpow_succ _ nN). 
Qed.

Lemma expansion_prop9 f b k: expansion f b k ->
   (expansion_value f b) <c (b ^c k).
Proof. 
move=> Exp. 
have kN: natp k by move:  Exp => [bN kN _ _].
move: k kN f Exp.
apply: Nat_induction.
  move: clt_01 => H g [bN _ b2 [fgf df _]].
  rewrite cpowx0 /expansion_value df/csumb csum_trivial; aw; trivial.
move=> n nN pn g eg.
have cn: (cardinalp n) by fprops. 
rewrite (expansion_prop7 eg cn).
have er:= (expansion_prop5 eg cn).
have [bN _ b2 [fgf df vg]] := eg.
move: (pn _ er). 
rewrite cpow_succ //.
move: (expansion_prop3 er).
set (a0:= expansion_value (restr g n) b).
set (b0:= b ^c n); set c0:= (Vg g n) *c b0.
move => a0N h.
have p1: (Vg g n) <c b by  apply: vg; rewrite df; apply:Nsucc_i.
have cN:= NS_lt_nat p1 bN.
have b0N: natp b0 by apply: NS_pow.
have le1: (a0 +c c0) <c (b0 +c c0).
  apply: csum_Mlteq => //;rewrite /c0; fprops.
suff le2: (b0 +c c0) <=c (b0 *c b) by apply: clt_leT le1 le2.
have cb: cardinalp b0 by fprops.
have ->: b0 +c c0 = b0 *c (csucc (Vg g n)).
  rewrite (Nsucc_rw cN) cprodDr (cprod1r cb) cprodC csumC //. 
by apply: cprod_Meqle;apply /(cleSltP cN).
Qed.

Lemma expansion_prop10 f b k: cardinalp k ->
  expansion f b (csucc k) ->
  cdivision_prop (expansion_value f b) (b ^c k) (Vg f k)
  (expansion_value (restr f k) b).
Proof.
move=> ck ie;split.
  by rewrite csumC cprodC; apply: expansion_prop7.
by apply: expansion_prop9; apply: expansion_prop5.
Qed.

Lemma expansion_unique f g b k: 
  expansion f b k -> expansion g b k -> 
  expansion_value f b = expansion_value g b -> f = g. 
Proof.
move=> ef eg sm.
have kN: natp k by move: eg => [_ kN _ _ ].
move: k kN f g sm ef eg.
apply: Nat_induction.
  rewrite /expansion.
  move=> f1 g1 sv [bN _ _ [fgf df _]] [_ _ _ [fgg dg _]].
  by apply: fgraph_exten; [exact | exact | ue | rewrite df;move=> x /in_set0 ].
move=> n nN pn f g sv ef eg.
have cn: cardinalp n by fprops. 
have p1:= (expansion_prop10 cn ef).
have p2:= (expansion_prop10 cn eg).
have er1:=(expansion_prop5 ef cn).
have er2:= (expansion_prop5 eg cn).
have egN :=(expansion_prop3 eg).
have q1N:= (expansion_prop6 ef cn).
have q2N:= (expansion_prop6 eg cn).
have r1N:= (expansion_prop3 er1).
have r2N:= (expansion_prop3 er2).
rewrite sv in p1.
have bN: natp b by move: ef =>  [bN _].
have cpN: natp (b ^c n) by fprops.
have bnz: (b ^c n <> \0c).
  have [_ b0]: (\0c <c b) by move: ef => [_ _ /(cle_ltT cle_01) ].
   by apply: cpow_nz => bz; case: b0.
move: (cdivision_unique egN cpN q1N r1N q2N r2N bnz p1 p2)=> [pt r].
have aux: (restr f n = restr g n) by apply: pn =>//.
move:ef eg=> [_ _ _ [fgf df _]] [_ _ _ [fgg dg _]].
apply: fgraph_exten; [ exact | exact | ue | move=> x xdf /=].
case: (equal_or_not x n); first by move => ->.  
move=> xn.
have xc: (inc x n).
  by move:xdf; rewrite df (succ_of_nat nN); case/setU1_P.
have <-: (Vg (restr f n) x = Vg f x) by rewrite LgV.
have <-: (Vg (restr g n) x = Vg g x) by rewrite LgV.
ue.
Qed.


Lemma expansion_prop11 f g b k: cardinalp k ->
  expansion f b (csucc k) -> expansion g b (csucc k) -> 
  (Vg f k) <c (Vg g k) ->
  (expansion_value f b) <c (expansion_value g b).
Proof. 
move=>  ck ef eg ltk.
rewrite (expansion_prop7 ef ck) (expansion_prop7 eg ck).
have ef1:= (expansion_prop5 ef ck).
have eg1:=(expansion_prop5 eg ck).
move: (expansion_prop9 ef1). 
move: (expansion_prop3 ef1). 
move: (expansion_prop3 eg1).
set u:= expansion_value _ _; set v:= expansion_value _ _.
move=> uN vN vp.
have kn:= (expansion_prop4 ef ck).
have fN:=(expansion_prop6 ef ck).
have gN:=(expansion_prop6 eg ck).
set (B:= b ^c k).
have bN: natp b by move: ef => [h _].
have BN: natp B by rewrite /B; fprops.
apply: (@clt_leT (B +c  ((Vg f k) *c B))).
  apply: csum_Mlteq; fprops.
apply: (@cleT ((Vg g k) *c B)); last by apply:csum_Mle0; fprops.
move /(cleSltP fN): ltk  => ltk.
move: (cprod_Mleeq B ltk). 
by rewrite (Nsucc_rw fN) cprodDl (cprod1l (CS_nat BN)) csumC.
Qed.

Lemma expansion_restr1 f b k l:
  expansion f b k -> l <=c k ->
  expansion (restr f l) b l.
Proof.
move=> [bN kN b2 [fgf df vg]] lk.
have lN:= NS_le_nat lk kN.
split; fprops; split; aww => i idx; rewrite LgV//; apply: vg; rewrite df.
by apply: (proj33 lk).
Qed.



Lemma expansion_restr2 f b k l:
  expansion f b k -> l <=c k ->
  (forall i, l <=c i -> i <c k -> Vg f i = \0c) ->
  expansion_value (restr f l) b = expansion_value f b.
Proof.
move=> ef lk p.
pose g i := expansion_value (restr f i) b.
move: (ef) => [bN kN b2 [fgf df vg]].
have ->: expansion_value f b = g k by  rewrite  /g -df restr_to_domain //. 
rewrite -/(g _).
have H i: l <=c i -> i <c k -> g i = g (csucc i).
  move => lli lik; move: (NS_lt_nat lik kN) => iN.
  move/(cleSltP iN): (lik) =>  sik.
  move:(expansion_restr1 ef sik) => eF.
  rewrite /g (expansion_prop7 eF (CS_nat iN)).
  rewrite (double_restr _ (proj33 (cleS iN))) (restr_ev _ (Nsucc_i iN)).
  rewrite (p i lli lik) cprod0l csum0r //; apply: CS_cardinal.
have H': forall i, natp i -> l <=c i -> i <=c k -> g l = g i.
  apply: Nat_induction; first by move => /cle0 ->.
  move => i iN h lsi /(cleSltP iN) lik.
  case: (cle_eqVlt lsi); [ by move -> | move/(cltSleP iN) => li].
  by rewrite - (H _ li lik) (h  li (proj1 lik)).
by rewrite -/(g _ )(H' _ kN lk (cleR (proj32 lk))).
Qed.

Lemma expansion_prop12 f g b kf kg l n: 
  n <=c kf -> n <=c kg ->  l <c n ->
  (forall i, n <=c i -> i <c kf -> Vg f i = \0c) ->
  (forall i, n <=c i -> i <c kg -> Vg g i = \0c) ->
  (forall i, l <c i ->  i <c n -> Vg f i = Vg g i) ->
  expansion f b kf -> expansion g b kg -> 
  (Vg f l) <c  (Vg g l) ->
  (expansion_value f b)  <c (expansion_value g b).
Proof. 
move=> nkf nkg ln pf pg pfg ef eg vl.
move: (expansion_restr1 ef nkf).
rewrite -(expansion_restr2 ef nkf pf). 
move: (expansion_restr1 eg nkg).
rewrite -(expansion_restr2 eg nkg pg). 
set F :=  (restr f n).
set G :=  (restr g n).
move=> eG eF; clear pf pg.
move: (ef) =>  [bN kfN _ [fgf df vf]].
move: (eg) => [_ kgN b2 [fgg dg vg]].
have nN:= NS_le_nat nkf kfN.
have lN:= NS_lt_nat ln nN.
have pFG:  forall i, l <c i -> i <c n -> Vg F i = Vg G i.
  move=> i i1 i2; move: (pfg _  i1 i2).
  have ii: inc i n by apply /NltP.
  by rewrite /F/G !LgV //.
have vL:  (Vg F l) <c (Vg G l).
  have ii: inc l n by  apply /NltP. 
  by rewrite /F/G !LgV.
clear pfg vl ef eg fgg fgf df dg vf vg.
set fi := fun i =>  expansion_value (restr F i) b.
set gi := fun i =>  expansion_value (restr G i) b.
move: (eF) (eG) =>  [_ _ _ [fgf df vf]] [_ _ _ [fgg dg vg]].
have <-: (fi n = expansion_value F b) by rewrite /fi -df restr_to_domain.
have <-: (gi n = expansion_value G b) by rewrite /gi -dg restr_to_domain.
pose r i := (fi i) <c (gi i).
have cl2: natp (csucc l) by fprops.
have cl0: (csucc l) <=c n by apply /cleSltP.
apply: (Nat_induction3 (r:=r) cl2 nN _ _ cl0 (cleR (proj31 nkf))).
  rewrite /r /fi /gi.
  have ef1 := (expansion_restr1 eF cl0).
  have eg1 := (expansion_restr1 eG cl0).
  have il:= (Nsucc_i lN).
  apply: (expansion_prop11 (CS_nat lN) ef1 eg1).
  rewrite LgV// [X in _ <c X]  LgV //.
move => i li ik ri.
have iN:= NS_lt_nat ik nN.
have lsin: (csucc i) <=c n by apply /cleSltP.
have ssin:= (proj33 lsin).
have issi:= (cleS iN).
have ssi:= (proj33 issi).
have isi:= (Nsucc_i iN).
move:(expansion_restr1 eF lsin).
move:(expansion_restr1 eG lsin).
set f1 := (restr F (csucc i)).
set g1 := (restr G (csucc i)).
move=> ef1 eg1; move: ri.
rewrite /r /fi /gi (expansion_prop7 ef1 (proj32 li)).
rewrite (expansion_prop7 eg1 (proj32 li)).
set f2 := (restr f1 i).
set g2 := (restr g1 i).
have si: sub (csucc i) (domain F) by rewrite df.
have sj: sub (csucc i) (domain G) by rewrite dg.
have ->: (restr F i = f2) by rewrite /f2 /f1 double_restr.
have ->: (restr G i = g2) by rewrite /g2 /g1 double_restr.
have ->: (Vg f1 i = Vg g1 i).
  rewrite /f1 /g1 LgV // [RHS] LgV //; apply: pFG=>//.
  apply/cleSlt0P; fprops.
have ef2 := (expansion_restr1 eg1 issi).
have eg2 := (expansion_restr1 ef1 issi).
apply: csum_Mlteq.
apply: NS_prod; fprops; apply: (expansion_prop1 ef1); fprops.
Qed.

Lemma expansion_prop13 f g b kf kg l:
  kf <=c l -> l <c kg ->
  expansion f b kf -> expansion g b kg -> 
  Vg g l <> \0c ->
  (expansion_value f b) <c (expansion_value g b).
Proof.
move=> le1 le2 ef eg vnz.
apply: (@clt_leT (b ^c kf)); first apply: (expansion_prop9 ef).
move: eg => [bN bK b2 [fgf df vg]].
rewrite /expansion_value /csumb.
set F:= Lg _ _.
have fgF: fgraph F by rewrite /F;fprops.
have dF: domain F = kg by rewrite /F -df; aw.
have alc: (forall x, inc x (domain F) -> cardinalp (Vg F x)).
  rewrite dF -df /F => x xdf; rewrite LgV //; fprops.
have ldf: inc l (domain F) by rewrite dF; apply /NltP.
set j:= singleton l.
have sj: sub j (domain F) by move => t /set1_P ->.
move: (csum_increasing1 sj). 
rewrite (csum_trivial4 _ _ ) (card_card (alc _ ldf)).
have ldg: inc l (domain g) by rewrite df; apply /NltP.
have bnz: b<> \0c by move=>h; rewrite h in b2; case: (clt0 b2).
apply:cleT; rewrite /F LgV//.
apply: (@cleT (b ^c l)); first apply: cpow_Mlele; fprops.
rewrite cprodC;apply: cprod_M1le; fprops.
Qed.

Lemma expansion_prop14 f g b kf kg:
  expansion f b kf -> expansion g b kg -> 
  (expansion_value f b) <c  (expansion_value g b) ->
  (exists l, [/\ kf <=c l, l <c kg & Vg g l <> \0c])
 \/ (
  exists l n, 
  [/\ n <=c kf, n <=c kg, l <c n &
  [/\ (forall i, n <=c i -> i <c kf -> Vg f i = \0c),
  (forall i, n <=c i -> i <c kg -> Vg g i = \0c) ,
  (forall i, l <c i ->  i <c n -> Vg f i = Vg g i) &
   (Vg f l) <c  (Vg g l)]]).
Proof. 
move=> ef eg lt.
have kfN:natp kf by move: ef => [_ h _].
have kgN:natp kg by move: eg => [_ h _].
have [n [nf ng nfg]]: exists n, 
   [/\ n <=c kf, n <=c kg & (n = kf \/ n = kg)].
  case: (NleT_ee kfN kgN)=> aux; [exists kf | exists kg];split;fprops.
have nN: natp n by case: nfg => ->. 
case: (p_or_not_p (forall i, n <=c i -> i <c kg -> Vg g i = \0c)); last first.
  move=> h.
  have [i [ni ik Vz]]:  (exists i, [/\ n <=c i, i <c kg & Vg g i <> \0c]).
    ex_middle h'; case: h => i i1 i2; ex_middle h''; case h'; exists i => //.
  left; exists i; split => //.
  case: nfg; [by move=> <- | move=> nk; case:(cltNge ik); ue ].
move=> pB; right.
case: (p_or_not_p (forall i, n <=c i -> i <c kf -> Vg f i = \0c));  last first.
  move=> h.
  have [i [ni ik Vz]]:  (exists i, [/\ n <=c i, i <c kf & Vg f i <> \0c]).
    ex_middle h'; case: h => i i1 i2;  ex_middle h''; case h'; exists i => //.
  have fi:  kg <=c i.
   case: nfg; [ move => nk; case: (cltNge ik); ue | by move=> <-]. 
  by move: (expansion_prop13 fi ik eg ef Vz) =>[ /(cltNge lt)].
move=> pA.
move: (ef) (eg) => [bN bK b2 [fgf df vf]][_ _ _ [fgg dg vg]].    
have pC: exists2 l, l <c n&  (Vg f l) <>  (Vg g l).
  have hf:= (expansion_restr2  ef nf pA).
  have hg:= (expansion_restr2  eg ng pB).
  ex_middle bad.
  have eq:  (restr f n = restr g n).
    have s1: sub n (domain g) by rewrite dg; apply: (proj33 ng).
    have s2: sub n (domain f) by rewrite df; apply: (proj33 nf).
    have drf: (domain (restr f n) =  n) by aw.
    have drg: (domain (restr g n) =  n) by aw.
    apply: fgraph_exten; fprops; first ue.
    rewrite drf => x xdf; rewrite !LgV //.  
    ex_middle nx; case: bad; exists x => //.
    by move: xdf => /(NltP nN).
  move: lt;rewrite -hf -hg eq; move => [_ ne]; case: ne; reflexivity.
have [l [lp ln Vl]]: exists l,
    [/\ (forall i, l <c i -> i <c n -> Vg f i = Vg g i),
      l <c n & (Vg f l) <> (Vg g l)].
  set z:= Zo Nat (fun l => l <c n /\ Vg f l <> Vg g l).
  have nz: nonempty z.
    move: pC => [l lp]; exists l; apply: Zo_i => //; apply: (NS_lt_nat lp nN).
  have pa: (forall a, inc a z -> cardinalp a) by move=> a /Zo_P [aN _ ]; fprops.
  have [wor sr]:= (wordering_cle_pr pa).
  have tor := (worder_total wor).
  have zc: sub z (Nint n) by move=> t /Zo_P [_ [p1 _]]; apply /NintP.
  have fsz: finite_set z by apply: (sub_finite_set zc); apply:  finite_Nint.
  have sw: sub z (substrate (graph_on cardinal_le z)) by rewrite sr; fprops.
  have or := proj1  wor.
  move: (finite_subset_torder_greatest tor fsz nz sw)=> [l []].
  rewrite iorder_sr //; move=> lz lp; exists l.
  move: (lz); move => /Zo_P [lN [ln Vl]]; split => //.
  move=> i li lin;  ex_middle h.
  have iN:= NS_lt_nat lin nN.
  have iz: inc i z by apply: Zo_i => //. 
  by move: (iorder_gle1  (lp _ iz)) => /graph_on_P1 [_  _ /(cltNge li)].
exists l; exists n; split => //.
have p1: cardinalp  (Vg f l).
  have ldf: (inc l (domain f)). 
   rewrite df; apply /NltP => //; apply:clt_leT ln nf.
  exact: (proj31_1 (vf _ ldf)). 
have p2: cardinalp  (Vg g l).
  have ldf: (inc l (domain g)). 
     rewrite dg; apply /NltP => //; apply:clt_leT ln ng.
   exact: (proj31_1 (vg _ ldf)). 
case: (cleT_el p2 p1) => // h.
have p3: (Vg g l) <c (Vg f l) by split => //; apply: nesym.
have lp' : forall i, l <c i -> i <c n -> Vg g i = Vg f i.
  by move=> i i1 i2; symmetry;move: (lp _ i1 i2).
case: (cltNge lt (proj1(expansion_prop12 ng nf ln pB pA lp' eg ef p3))).
Qed.

Lemma expansion_prop15 f g b n:
  expansion f b n -> expansion g b n -> 
  ( (expansion_value f b) <c  (expansion_value g b)
    <->  exists k, 
         [/\ k <c n, (Vg f k) <c  (Vg g k) &
          (forall i, k <c i ->  i <c n -> Vg f i = Vg g i)]).
Proof.
move => ha hb; split.
  case/(expansion_prop14 ha hb); first by move => [l [sa /(cleNgt sa) sb _]].
  move => [l [m [hc hd he [hf hi hj hk]]]]; exists l; split => //.
    apply:clt_leT he hc.
  move => i la lb; case: (cleT_el (proj31 hc) (proj32_1 la)) => lc.
      rewrite hf // hi //.
   by apply: hj.
move => [k [hc hd he]].
have nn := (cleR (proj32_1 hc)).
by apply:(expansion_prop12 nn nn hc) he ha hb hd => i la /(cleNgt la).
Qed.

Definition exp_boundary f k := 
   (k = \0c \/ (k <> \0c /\  Vg f (cpred k) <> \0c)).

Definition expansion_of f b k a := 
   expansion f b k /\ expansion_value f b = a.

Definition expansion_normal_of f b k a := 
  expansion_of f b k a /\ (exp_boundary f k).


Definition sub_fgraphs A B :=  unionf (\Po A) (gfunctions ^~ B).

Lemma sub_fgraphsP A B f:
   inc f (sub_fgraphs A B) <-> exists2 C, sub C A & inc f (gfunctions C B).
Proof.
split.
  by move/setUf_P => [z /setP_P zx h ] ; exists z.
move => [C /setP_P ca cb]; apply /setUf_P; ex_tac.
Qed.

Lemma expansion_bounded1 f k b : expansion f b k ->
  inc f (sub_fgraphs Nat b).
Proof.
move => [bN kn _  [pd pe pf]].
apply /sub_fgraphsP; exists k; first by move => t; apply:(NS_inc_nat kn). 
apply/gfunctions_P2; split => // t/(range_gP pd) [x /pf xdf ->].
apply /(oltP (OS_nat bN)); exact:(oclt xdf).
Qed.


Section TheExpansion.
Variable b: Set.
Hypothesis bN: natp b.
Hypothesis bp: \1c <c b.

Lemma expansion_exists1 a k: 
  natp k -> natp a -> a <c (b ^c k) ->
  exists f, expansion_of f b k a.
Proof.
move=> kN; move: k kN a.
apply: Nat_induction.
  rewrite cpowx0 => c cN c1.
  exists (Lg emptyset (fun _ => \0c)); hnf; saw.
    split;fprops; split; fprops.
      by aw.
    by aw; move=> i /in_set0.
  rewrite /expansion_value/csumb; aw; rewrite csum_trivial; aw; trivial.
  by move: c1; rewrite - succ_zero; move / (cltSleP NS0) => /cle0 ->.
move=> n nN pn c cN cp.
set (b0:= b ^c n). 
have b0N: natp b0  by  rewrite /b0; fprops.
have Bz: (b0 <> \0c).
  have [_ /nesym bnz]:=(clt_ltT clt_01 bp).
  apply: (cpow_nz bnz). 
move: (cdivision cN b0N Bz) => [qN rN [aux lt]].
rewrite /b0 in lt.
move: (pn _ rN lt) => [f [ise ev]].
have p1: (b0 *c  (c %/c b0)) <c (b0 *c b).
  have p2: ((b0 *c  (c %/c b0)) <=c c). by rewrite {2} aux; apply: csum_M0le; fprops. 
  have p3: natp (b0 *c  (c %/c b0)) by fprops. 
  rewrite /b0 - cpow_succ -/b0; fprops; apply:cle_ltT p2 cp.
move: (cprod_lt2l b0N qN bN p1) => qb.
move: (expansion_prop8 ise qN qb).
set F:= (Lg _ _).
move=> [s1 s2]; exists F;split => //.
by rewrite s2 ev {3} aux csumC /b0. 
Qed.

Lemma expansion_exists2 a: natp a -> exists k f, expansion_of f b k a.
Proof. 
move=> aN; exists a.
exact:(expansion_exists1 aN aN (cpow_M1lt (CS_nat aN) bp)).
Qed.

Lemma expansion_exists3 a: natp a -> exists k f, expansion_normal_of f b k a.
Proof.
move=> aN; move:(expansion_exists2 aN) => [k [f [pa pb]]].
move: (pa) => [ha hb hc hd].
move:(hd) => [he hf hg].
pose prop l := l <=c k /\ forall i, l <=c i -> i <c k -> Vg f i = \0c.
have pc: forall l, prop l ->  expansion_of (restr f l) b l a.
  move => l [lk lp].
  have lN := (NS_le_nat lk hb).
  split; last by rewrite (expansion_restr2 pa lk lp) pb.
  split => //; aw; split => //; fprops => i id; rewrite LgV//.
  move/(NltP lN):id => il; have ik := (clt_leT il lk).
  by apply: hg; rewrite hf; apply/(NltP hb). 
have neA: prop k by split; fprops => i ia /(cleNgt ia).
case: (least_int_prop2 hb neA).
  by move/pc => h;exists \0c, (restr f \0c); split => //; left.
set l := cpred _; move => [lN slA naA].
move: (pc _ slA) => h.
have sa:= (Nsucc_i lN).
exists (csucc l), (restr f (csucc l)); split => //; right.
rewrite  (cpred_pr2 lN); split; [by apply: succ_nz | rewrite LgV// => fz].
move:slA => [sc sd].
case naA; split; first exact:(cleT (cleS lN) sc).
move => i i1 i2; case (equal_or_not l i) => eil; first by rewrite - eil.
by apply: sd => //; apply/(cleSltP lN).
Qed.

Lemma expansion_unique1 a f k f' k':
  expansion_normal_of f b k a -> expansion_normal_of f' b k' a ->
  f = f' /\ k = k'.
Proof.
move =>  [[ha hb] hc] [[ha' hb'] hc'].
have kN: natp k by case: ha.
have kN': natp k' by case: ha'.
wlog: k k' f f' ha hb hc ha' hb' hc' kN kN'/ k <c k'.  
  case: (NleT_ell kN' kN) => h H; last by apply:H.
    rewrite h in ha'; rewrite - hb' in hb.
    split => //; exact: (expansion_unique ha ha' hb).
  by case:(H _ _ _ _ ha' hb' hc' ha hb  hc kN' kN h) => [-> ->]. 
move => h.
case: hc'; first by move => e1; rewrite e1 in h; case: (clt0 h). 
  move => [e1 e2].
  move: (cpred_pr kN' e1) => [sa sb].
  have k1: k <=c (cpred k') by apply /(cltSleP sa); rewrite - sb.
  have k2: (cpred k') <c k' by rewrite {2} sb; apply: cltS.
  by move: (proj2 (expansion_prop13 k1 k2 ha ha' e2)); rewrite hb hb'.
Qed.

Definition the_expansion a :=
  select (fun z => expansion_normal_of z b (cardinal (domain z)) a)
     (sub_fgraphs Nat b). 

Lemma the_expansion_pr a (z := the_expansion a):
   natp a -> 
   expansion_normal_of z b (cardinal (domain z))  a.
Proof.
pose p z:= expansion_normal_of z b (cardinal (domain z))  a.
set E := (sub_fgraphs Nat b).
move => aN.
have sa: (exists2 x, inc x E & p x).
  move: (expansion_exists3 aN) => [k [f etc]].
  have cdf: k = cardinal (domain f).
    by move: etc => [[[_ hb _ [_ -> _]] _] _]; rewrite (card_nat hb).
  move: (expansion_bounded1 (proj1 (proj1 etc))) => xEZ; ex_tac.
  by rewrite /p - cdf.
have sb: singl_val2 (inc^~ E) p.
  move => f1 f2 _ pf1 _  pf2; exact: (proj1 (expansion_unique1 pf1 pf2)).
by move: (select_pr sa sb) => []. 
Qed.

Lemma the_expansion_zero: the_expansion \0c = emptyset.
Proof.
move: (the_expansion_pr NS0) => sa.
have hh: exp_boundary emptyset \0c by left.
suff: expansion_normal_of emptyset b \0c \0c.
  move => sb; exact (proj1 (expansion_unique1 sa sb)).
have H: expansion_value emptyset b = \0c.
  by rewrite /expansion_value domain_set0; apply: csum_trivial; aw.
split; fprops;split => //; split;fprops; split; aw => //. 
+ apply: fgraph_set0.
+ by move => i /in_set0.
Qed.

 
Lemma the_expansion_digit a: 
  a <> \0c -> a <c b -> the_expansion a = singleton (J \0c a).
Proof.
move => abz alb.
have aN :=(NS_lt_nat alb bN).
have n1:= NS1.
move: (the_expansion_pr aN) => sa.
move: (simple_fct2 \0c a); set f := singleton (J \0c a).
move => [ra rb rc rd re].
have rf:Vg f \0c *c b ^c \0c = a by rewrite rd cpowx0 (cprod1r (CS_nat aN)).
have rg: expansion_value f b = a.
  by rewrite /expansion_value rb csum_trivial3 rf (card_nat aN).
suff: expansion_normal_of f b \1c a.
  move => sb; exact (proj1 (expansion_unique1 sa sb)).
split; last by right; split; [ apply: card1_nz | by rewrite cpred1 rd].
split => //; split => //; rewrite rb; split => //.
move => i /set1_P ->; ue.
Qed.


Definition the_contraction a :=  csum (the_expansion a).

Lemma the_contraction_zero: the_contraction \0c = \0c.
Proof.
by rewrite /the_contraction the_expansion_zero csum_trivial // domain_set0.
Qed.


Lemma the_contraction_digit  a: a <c b -> the_contraction a = a.
Proof.
move => lab.
case: (equal_or_not a \0c) => anz. 
  by rewrite anz; exact:the_contraction_zero.
rewrite /the_contraction - {2} (card_card (proj31_1 lab)) /the_contraction.
move: (simple_fct2 \0c a) => [_ _ _ _ re].
by rewrite (the_expansion_digit anz lab) re  -/(csumb _ _ ) csum_trivial3.
Qed.

Lemma the_contraction_non_digit a: b <=c a -> natp a ->
   the_contraction a <c a.
Proof.
move => pa pb; rewrite /the_contraction.
move: (the_expansion_pr pb).
set f := (the_expansion a);move => [[pc pd] pe].
case: pe.
   move => /card_nonempty cdf; rewrite csum_trivial //.
   exact: (clt_leT (clt_ltT clt_01 bp) pa).
move: (pc) => [pg ph pi [pk1 pk2 pk3]] [pl pm].
move: (cpred_pr ph pl); set k1:= cpred _; move => [pn po].
move:pm; rewrite po; rewrite (cpred_pr2 pn) => pm.
set g := (Lg (domain f) (fun i => Vg f i *c b ^c i)).
have fsdf: finite_set (domain f) by rewrite /finite_set po; fprops.
have dfdg: domain f = domain g by rewrite /g; aw.
have qa:finite_int_fam f.
  split => //; move => i /pk3 h; apply:(NS_lt_nat h pg).
have qb:finite_int_fam g.
  rewrite /g; saw; hnf; aw => i idf.
  rewrite LgV //; move: (proj1 qa _ idf) => sa; apply/NS_prod => //.
  apply /NS_pow => //. 
  by move: idf; rewrite pk2 po; move/(NleP pn) => le; move:(NS_le_nat le pn).
rewrite - pd /expansion_value /csumb.
have bsp:= (clt_ltT (clt_01) pi).
apply: (finite_sum_lt qa qb); aw; trivial.
  rewrite /g; move => i idf;rewrite LgV //; apply: cprod_M1le.
     exact: (CS_nat (proj1 qa _ idf)).
  by apply: cpow_nz => bz; case: (proj2 bsp).
have kh1:inc k1 (domain f). 
  by rewrite pk2; apply/(NltP ph); rewrite po; apply:cltS.
have nk1: natp (Vg f k1) by apply(proj1 qa _ kh1).
have nk3: natp (b ^c k1) by fprops.
case: (equal_or_not k1 \0c) => k1z.
  have ddf: domain f = singleton \0c.
    by rewrite pk2 po k1z succ_zero.
  have zdf: inc \0c (domain f) by rewrite ddf; fprops.
  have aux:= (CS_nat (proj1 qa _ zdf)).
  have rs: Vg f \0c *c b ^c \0c = Vg f \0c.
    by rewrite cpowx0 (cprod1r aux).
  case:(cleNgt pa);move: pd (pk3 _ zdf).
  by rewrite /expansion_value ddf (csum_trivial3) rs (card_card aux) => ->.
have pp:= (clt_leT pi (cpow_Mle1 (CS_nat pg) k1z)).
exists k1 => //; rewrite /g; rewrite LgV //; apply:cprod_M1lt => //. 
Qed.   

Lemma the_contraction_non_zero a: natp a -> a <> \0c ->
   the_contraction a <> \0c.
Proof.
move => aN ap; rewrite /the_contraction.
move: (the_expansion_pr aN).
set f := (the_expansion a);move => [[pc pd] pe].
case: pe.
   move => /card_nonempty cdf; move: ap ; rewrite - pd. 
   by rewrite /expansion_value/csumb csum_trivial //; aw.
move: (pc) => [pg ph pi [pk1 pk2 pk3]] [pl pm] sz.
move: (cpred_pr ph pl); set k1:= cpred _; move => [pn po].
have kh1:inc k1 (domain f). 
  by rewrite pk2; apply/(NltP ph); rewrite po; apply:cltS.
have ckf: cardinalp (Vg f k1) by  move/pk3: kh1 => [[]].
by move: (csum_increasing6 ckf kh1); rewrite sz => /cle0.
Qed.

Definition contraction_rec a := 
  induction_defined (the_contraction) a.
Definition contraction_rep a := Vf (contraction_rec a) a.

Lemma contraction_rec0 a: Vf (contraction_rec a) \0c = a.
Proof.
exact: (proj43 (induction_defined_pr (the_contraction) a)).
Qed.

Lemma contraction_rec_succ a n: natp n -> 
  Vf (contraction_rec a) (csucc n) = the_contraction (Vf (contraction_rec a) n).
Proof.
exact: (proj44 (induction_defined_pr (the_contraction) a) n).
Qed.

Lemma NS_contraction_rec a n: natp a -> natp n ->
   natp (Vf (contraction_rec a) n).
Proof.
move => aN nN; move: n nN a aN; apply: Nat_induction.
  by move => a aN; rewrite contraction_rec0.
move => n nN Hrec a /Hrec aN; rewrite (contraction_rec_succ _ nN).
case: (NleT_el bN aN) => cnb.
  by move:(the_contraction_non_digit cnb aN) => /(NS_lt_nat); apply.
by rewrite (the_contraction_digit cnb).
Qed.

Lemma contraction_rec_non_zero a n: natp n -> natp a -> a <> \0c ->
   (Vf (contraction_rec a) n) <> \0c.
Proof.
move => nN; move: n nN a; apply:Nat_induction.
  by move => a _ anz; rewrite contraction_rec0.
move => n nN Hrec a aN anz; rewrite (contraction_rec_succ _ nN).
apply:(the_contraction_non_zero (NS_contraction_rec aN nN) (Hrec _ aN anz)). 
Qed.

Lemma contraction_rec_succ' a n: natp n -> 
  Vf (contraction_rec a) (csucc n) = Vf (contraction_rec (the_contraction a)) n.
Proof.
move => nN; move: n nN a; apply: Nat_induction.
  by move => a; rewrite (contraction_rec_succ _ NS0) ! contraction_rec0.
move => n nN Hrec a.
by rewrite (contraction_rec_succ _ (NS_succ nN)) Hrec contraction_rec_succ.
Qed.

Lemma contraction_rec_succ'' a n m: natp n -> natp m ->
  Vf (contraction_rec a) (n +c m) = 
     Vf (contraction_rec (Vf (contraction_rec a) n)) m.
Proof.
move => nN mN; move: m mN n nN.
apply: Nat_induction.
  move => n nN; rewrite contraction_rec0 csum0r; fprops.
move => m mN Hrec n nN.
rewrite (csum_nS _ mN) (contraction_rec_succ _ (NS_sum nN mN)).
rewrite (Hrec _ nN) contraction_rec_succ //.
Qed.

Lemma contraction_rep_dig a : natp a -> contraction_rep a <c b.
Proof.
move:a.
suff: forall a, natp a -> forall c, c <=c a -> contraction_rep c <c b.
  move => H a aN; exact: (H a aN a (cleR (CS_nat aN))).
apply: Nat_induction.
  move => c /cle0 ->; rewrite /contraction_rep contraction_rec0.
  exact:(clt_ltT (clt_01) bp).
have H: forall n, natp n -> forall a, a <c b -> Vf (contraction_rec a) n = a.
   apply: Nat_induction; first by move => a  _; rewrite contraction_rec0.
   move => n nN Hrec a ab; rewrite (contraction_rec_succ' _ nN).
   rewrite (the_contraction_digit ab); exact: Hrec.
move => n nN Hrec c csn; case: (equal_or_not c (csucc n)); last first.
   move => h;move /(cltSleP nN): (conj csn h); exact: Hrec.
have snN:=(NS_succ nN). 
move => ->; case: (NleT_el bN snN) => cnb; last first.
  by rewrite/contraction_rep (H _ snN _ cnb).
move:(the_contraction_non_digit cnb snN) => /(cltSleP nN).
rewrite /contraction_rep (contraction_rec_succ' _ nN).
set x := the_contraction (csucc n) => xn.
move:  (NS_le_nat xn nN) (NS_diff x nN) (Hrec _ xn) => ha hb hc.
rewrite -(cdiff_pr xn) (contraction_rec_succ'' _ ha hb).
by rewrite -/(contraction_rep _) (H _ hb _ hc).
Qed.

Lemma contraction_rep_non_zero a: natp a -> a <> \0c ->
   (contraction_rep a) <> \0c.
Proof. by move => pa pb; apply:(contraction_rec_non_zero pa pa pb). Qed.
 
End TheExpansion.

(** Equality modulo n *)

Notation "m = n %c[mod d ]" := (m %%c d = n %%c d)
   (at level 70, n at next level,
   format "'[hv ' m '/'  =  n '/'  %c[mod  d ] ']'").


Definition eqmod B a b:=  a = b %c[mod B].

Section ModuloProps.
Variable B: Set.
Hypothesis BN: natp B.
Hypothesis Bnz: B <> \0c.


Lemma eqmod_equivalence (R:= graph_on (fun a b =>  a = b %c[mod B]) Nat):
    equivalence_on  R Nat.
Proof.
split; last by apply: graph_on_sr => a.
apply: equivalence_from_rel; split.
  by move => a b ab.
by move => b a c; rewrite /eqmod => -> ->.
Qed.

Lemma crem_prop a b: natp a -> natp b ->
  B *c a +c b = b %c[mod B].
Proof. 
move=> aN bN.
move: (cdivision bN BN Bnz). 
set q := b %/c B; set r := b %%c B.
move=> [q1N r1N [aeq r1p]]. 
rewrite aeq csumA - cprodDr.
set q2:= (a +c q).
have q2N: natp q2 by apply: NS_sum.
have dp: (cdivision_prop ((B *c q2) +cr) B q2 r) by split. 
by move: (cquorem_pr (NS_sum (NS_prod BN q2N) r1N) BN q2N r1N dp) => [_].
Qed.

Lemma crem_sum a b: natp a -> natp b -> 
   a +c b = a %%c B +c b %%c B %c[mod B].
Proof.
move=> aN bN.
move: (cdivision aN BN Bnz) (cdivision bN BN Bnz).
set q1:= a %/c B; set q2:= b %/c B; set r1:= a %%c B; set r2:= b %%c B.
move=> [q1N r1N [aeq r1p]][q2N r2N [beq r2p]].
rewrite aeq beq csumACA - cprodDr; apply: crem_prop; fprops.
Qed.

Lemma crem_prod a b: natp a -> natp b ->
 a *c b = (a %%c B) *c (b %%c B) %c[mod B].
Proof.
move=> aN bN. 
move: (cdivision aN BN Bnz) (cdivision bN BN Bnz).
set q1:= a %/c B; set q2:= b %/c B; set r1:= a %%c B; set r2:= b %%c B.
move=> [q1N r1N [aeq r1p]][q2N r2N [beq r2p]].
rewrite aeq beq cprodDr (cprodC B q2) cprodA (cprodC _ B).
rewrite (cprodDl r2) - cprodA csumA - cprodDr - aeq.
by apply: crem_prop ; [apply: NS_sum | ]; apply: NS_prod. 
Qed.

Lemma eqmod_sum a b a' b': natp a -> natp b ->
  natp a' -> natp b' -> 
  a = a' %c[mod B] -> b = b' %c[mod B] -> a +c b = a' +c b' %c[mod B].
Proof.
move=> aN bN a'N b'N e1 e2.
rewrite (crem_sum aN bN) e1 e2 (crem_sum a'N b'N); reflexivity.
Qed.

Lemma eqmod_prod a b a' b': natp a -> natp b ->
  natp a' -> natp b' -> 
  a = a' %c[mod B] -> b = b' %c[mod B] -> a *c b = a' *c b' %c[mod B].
Proof. 
move=> aN bN a'N b'N  e1 e2.
rewrite (crem_prod aN bN) (crem_prod a'N b'N) e1 e2;reflexivity.
Qed.
 
Lemma eqmod_rem a: natp a -> a =  a %%c B %c[mod B].
Proof. 
move=> aN; rewrite {1} (cdiv_pr aN BN); apply: crem_prop; fprops.
Qed.

Lemma eqmod_succ  a a': natp a -> natp a' ->
   a = a' %c[mod B] -> csucc a = csucc a' %c[mod B].
Proof. 
move=> aN a'N  e1.
rewrite !csucc_pr4; fprops; apply: eqmod_sum => //; fprops.
Qed.

Lemma eqmod_pow1  a n: natp a -> natp n ->
   a = \1c %c[mod B] -> a ^c n = \1c %c[mod B].
Proof. 
move=> aN nN h; move: n nN.
apply: Nat_induction; first by rewrite cpowx0.
move=> n nN h1.
move: (eqmod_prod (NS_pow aN nN) aN NS1 NS1 h1 h).
rewrite (cpow_succ _ nN) (cprod1r); fprops.
Qed.

Lemma eqmod_pow2 a b n: natp a -> natp b -> natp n ->
   a = \1c %c[mod B] -> b *c a ^c n = b %c[mod B].
Proof.
move=> aN bN nN h.
move: (eqmod_pow1 aN nN h) => h2.
have aux: eqmod B b b by [].
move: (eqmod_prod bN (NS_pow aN nN) bN NS1 aux h2).
rewrite cprod1r; fprops.
Qed.

Lemma eqmod_pow3  f b k:  expansion f b k ->
  b = \1c %c[mod B] -> expansion_value f b = csum f %c[mod B].
Proof. 
move=> ep b1.
have kN: natp k by move: ep => [bN kN _].
move: k kN f ep.
apply: Nat_induction.
  move=> g [bN _ b2 [fgf df _]].
  by rewrite /expansion_value/csumb df !csum_trivial //;  aw.
move=> n nN pn g eg.
have cn: (cardinalp n) by fprops. 
rewrite (expansion_prop7 eg cn).
move: (expansion_prop5 eg cn) => er.
move: (eg) =>  [bN _ _ [fgg dg _]].
move: (NS_succ nN) => snN.
have si: sub n (domain g) by rewrite dg; apply (proj33 (cleS nN)).
have ->: (csum g = (csum (restr g n)) +c  (Vg g n)).
  pose h w := \0c +c (Vg g w).
  have hp: forall x, inc x (domain g) -> h x = Vg g x.
    move=> x; rewrite dg; move /(NltP snN) => p1.
    move: (expansion_prop1 eg p1) => p2.
    by rewrite /h Nsum0l.
  move: (induction_on_sum h nN); rewrite /csumb.
  have ->: h n = Vg g n by apply: hp; rewrite dg; apply:Nsucc_i.
  have ->: (Lg (csucc n) h = g).
    apply: fgraph_exten; fprops; first by aw. 
    aw; move=> x xd /=; rewrite LgV //; apply: hp; ue.
  have -> //: (Lg n h = (restr g n)). 
    apply: Lg_exten => x xb;  apply: (hp _ (si _ xb)).
have p1: natp (Vg g n) by apply: (expansion_prop1 eg (cltS nN)).
have p2: natp ((Vg g n) *c  (b ^c n)).
   apply: (NS_prod p1 (NS_pow bN nN)).
have p3: natp (csum (restr g n)). 
  apply: finite_sum_finite_aux; last by exact.
  split => //. 
    move=> i; rewrite dg; move /(NltP snN).
    apply:  (expansion_prop1 eg).
  by rewrite dg; apply: finite_set_nat.
apply: (eqmod_sum (expansion_prop3 er) p2 p3 p1 (pn _ er)).
apply: (eqmod_pow2 bN p1 nN b1).
Qed.


End ModuloProps.

Lemma crem_succ a B: natp a -> natp B -> \1c <c B ->
  csucc a = csucc (a %%c B) %c[mod B].
Proof.
move => aN BN Bp.
have Bnz: B <> \0c by move => h; apply:(@clt0 \1c); rewrite - h.
move:(crem_sum BN Bnz aN NS1).
by rewrite - (crem_small BN Bp) - (Nsucc_rw aN) - (Nsucc_rw (NS_rem B aN)).
Qed.


Definition card_five := csucc card_four.
Definition card_six := csucc card_five.
Definition card_seven := csucc card_six.
Definition card_eight := csucc card_seven.
Definition card_nine := csucc card_eight.
Definition card_ten := csucc card_nine.
Notation "\10c" := card_ten.
Notation "\9c" := card_nine.
Notation "\5c" := card_five.
Notation "\6c" := card_six.
Notation "\7c" := card_seven.

Lemma card3_nz: \3c <> \0c.
Proof. by apply: succ_nz. Qed.

Lemma card9_nz: \9c <> \0c.
Proof. by apply: succ_nz. Qed.

Lemma NS5 : natp \5c.
Proof. apply: (NS_succ NS4). Qed.

Lemma NS6 : natp \6c.
Proof. apply: (NS_succ NS5). Qed.

Lemma NS7 : natp \7c.
Proof. apply: (NS_succ NS6). Qed.

Lemma NS9 : natp \9c.
Proof. apply: (NS_succ (NS_succ NS7)). Qed.

Lemma NS10 : natp \10c.
Proof. apply: (NS_succ NS9). Qed.

Lemma card_prod_3_3: \3c *c \3c = \9c.
Proof.
have aux n: natp n -> csucc (csucc (csucc n)) = n +c \3c.
  move => nN; rewrite /card_three (csum_nS _ NS2) - succ_one  (csum_nS _ NS1).
  by rewrite (Nsucc_rw nN).
rewrite [card_nine] (aux _ NS6) [card_six] (aux _ NS3).
rewrite{2}  /card_three  (Nsucc_rw NS2) cprodDr (cprod1r (CS_nat NS3)).
by rewrite cprodC csum_nn.
Qed.

Lemma card_mod_10_9: \10c = \1c %c[mod \9c].
Proof. 
have nnz:= card9_nz. 
rewrite  - succ_zero; apply:(eqmod_succ NS9 nnz NS9 NS0).
move: (crem_prop NS9 nnz NS1 NS0).
by rewrite (cprod1r (CS_nat NS9)) (csum0r (CS_nat NS9)).
Qed.

Lemma card_mod_10_3: \10c = \1c %c[mod \3c].
Proof.
rewrite /card_ten  (Nsucc_rw NS9) - card_prod_3_3.
exact: (crem_prop NS3 card3_nz NS3 NS1).
Qed.

Lemma cgt10_1: \1c <c \10c.
Proof.
apply /(cltSleP NS9); apply: cge1.
  apply: (CS_nat NS9).
apply: card9_nz.
Qed.

Definition expansion_ten f k := 
  [/\ natp k, fgraph f, domain f = k &
  forall i, inc i (domain f) -> (Vg f i) <c \10c].

Lemma divisibiliy_by_three f k: expansion_ten f k ->
  let g:= (Lg (domain f) (fun i=> (Vg f i) *c (\10c ^c i))) in
  csum g = csum f  %c[mod \3c].
Proof. 
move=> [p1 p2 p3 p4].
have ep: expansion f \10c k.
  split => //; [by apply: NS10 | apply:cgt10_1].
exact (eqmod_pow3 NS3 card3_nz ep card_mod_10_3).
Qed.


Lemma divisibiliy_by_nine f k: expansion_ten f k ->
  let g:= (Lg (domain f) (fun i=> (Vg f i) *c (\10c ^c i))) in
  (csum g) = (csum f) %c[mod \9c].
Proof.
move=> [p1 p2 p3 p4].
have ep: expansion f \10c k.
  split => //; [by apply: NS10 | apply:cgt10_1].
exact (eqmod_pow3 NS9 card9_nz ep card_mod_10_9).
Qed.

Lemma eqmod_contraction b a:
   natp a -> natp b -> b <> \0c ->
   a = the_contraction (csucc b) a %c[mod b].
Proof. 
move => aN bN bnz.
have sbN := NS_succ bN; have cb := (CS_nat bN).
have bg1: \1c <c (csucc b).
  apply /(cltSleP bN); exact:(cge1 (CS_nat bN) bnz).
move:(the_expansion_pr sbN bg1 aN).
rewrite/the_contraction; set f := the_expansion _ _.
move => [[ha hb] hc]; rewrite - hb.
apply:(eqmod_pow3 bN bnz ha).
rewrite (csucc_pr4 cb) - {1} (cprod1r cb); apply:crem_prop; fprops.
Qed.

Lemma eqmod_contraction_rep b a 
   (x := contraction_rep (csucc b) a) (y := a %%c b) :
   natp a -> natp b -> b <> \0c ->
   [/\ a = x %c[mod b],
    (a = \0c -> x = \0c) &
    (a <> \0c -> (y = \0c -> x = b) /\ (y <> \0c -> x = y))].
Proof.
move => aN bN bnz.
have sbN := NS_succ bN.
have bg1: \1c <c (csucc b).
  apply /(cltSleP bN); exact:(cge1 (CS_nat bN) bnz).
have hrec: forall n, natp n ->
  a = (Vf (contraction_rec (csucc b) a) n) %c[mod b].
  apply:Nat_induction; first by rewrite contraction_rec0.
  move => n nN; rewrite (contraction_rec_succ _ _ nN) => {1} ->.
  by apply:eqmod_contraction=> //;apply: NS_contraction_rec. 
have h: a = x %c[mod b] by apply:hrec. 
move:(contraction_rep_dig sbN bg1 aN); rewrite -/x.
move /(cltSleP bN) => lexb.
have xN := NS_le_nat lexb bN.
split => // ha.
  by rewrite /x ha /contraction_rep contraction_rec0.
move:(contraction_rep_non_zero sbN bg1 aN ha); rewrite -/x /y h => xnz.
case (equal_or_not x b) => xeb.
  by split => //; rewrite xeb (proj33(cdivides_itself bN)).
by rewrite-(crem_small bN (conj lexb xeb)).
Qed.

Lemma eqmod_contraction_rep9 a 
   (x := contraction_rep \10c a) (y := a %%c \9c) :
   natp a -> 
   [/\ a = x %c[mod \9c],
    (a = \0c -> x = \0c) &
    (a <> \0c -> (y = \0c -> x = \9c) /\ (y <> \0c -> x = y))].
Proof.
move => an.
apply:eqmod_contraction_rep => //; [ apply:NS9 | apply: card9_nz].
Qed.

(**  Even and odd integers; half and double *)
Definition evenp n := natp n /\ n %%c  \2c = \0c.
Definition oddp n := natp n /\ ~ (evenp n).

Lemma crem_02: \0c %%c \2c = \0c.
Proof. exact:  (crem_of_zero NS2). Qed.

Lemma crem_12: \1c %%c \2c = \1c.
Proof. exact:(sym_eq (crem_small NS2 clt_12)). Qed.

Lemma crem_22: \2c %%c \2c = \0c.
Proof. by move:(cdivides_itself NS2) => []. Qed.

Lemma oddp_alt n:  (oddp n <-> natp n /\ n %%c \2c = \1c).
Proof.
split => [] [nN on]; split => //.
  move: (cdivision nN NS2 card2_nz) => [ _ mN [_ /clt2]]; case => // h.
  by case:on.
case=> _; rewrite on; exact:card1_nz.
Qed.

Lemma even_zero: evenp \0c.
Proof. split; [fprops | exact crem_02]. Qed.

Lemma odd_one: oddp \1c.
Proof. split; [fprops | case => _]; rewrite crem_12; apply: card1_nz. Qed.

Lemma even_two: evenp \2c.
Proof. split; [fprops |  exact:crem_22]. Qed.

Lemma evenp_mod2 n: natp n -> (evenp n <-> n = \0c %c[mod \2c]).
Proof. by  move => nN; rewrite crem_02; split => //; case. Qed.

Lemma oddp_mod2 n: natp n -> (oddp n <-> n = \1c %c[mod \2c]).
Proof.
move => nN; rewrite crem_12; apply: (iff_trans (oddp_alt n)).
by split; [case|].
Qed.

Lemma succ_of_even n: evenp n -> oddp (csucc n).
Proof.
move => [nN h]; split; [fprops | case => _].
rewrite (crem_succ nN NS2 clt_12) h succ_zero crem_12; apply:card1_nz.
Qed.

Lemma succ_of_odd n: oddp n -> evenp (csucc n).
Proof.
move /(oddp_alt) => [nN sa].
by split;fprops; rewrite (crem_succ nN NS2 clt_12) sa succ_one crem_22.
Qed.


Lemma succ_of_evenP n: natp n -> (evenp n <-> oddp (csucc n)).
Proof.
move => nN; split; first by apply:succ_of_even.
move => h;ex_middle h';case: (proj2 h);exact:(succ_of_odd (conj nN h')).
Qed.

Lemma succ_of_oddP n: natp n -> (oddp n <-> evenp (csucc n)).
Proof.
move => nN; split; first by apply:succ_of_odd.
by move => h;case: (p_or_not_p (evenp n)) => // /succ_of_even [].
Qed.


Lemma csum_of_even a b: evenp a -> evenp b -> evenp (a +c b).
Proof.
move => [aN ae][bN be]; split; first by fprops.
by rewrite (crem_sum NS2 card2_nz aN bN) ae be (csum0r CS0) crem_02.
Qed.

Lemma csum_of_even_odd a b: evenp a -> oddp b -> oddp (a +c b).
Proof.
move => [aN ae] /oddp_alt [bN bo].
apply/(oddp_alt); split;first exact:(NS_sum aN bN).
by rewrite (crem_sum NS2 card2_nz aN bN) ae bo  (csum0l CS1) crem_12.
Qed.

Lemma csum_of_odd a b: oddp a -> oddp b -> evenp (a +c b).
Proof.
move => /(oddp_alt) [aN ao]  /(oddp_alt) [bN bo].
split; first fprops.
by rewrite (crem_sum NS2 card2_nz aN bN) ao bo csum_11 crem_22.
Qed.


Lemma csum_of_evenP n m: evenp n -> natp m  ->
  (evenp (n +c m) <-> evenp m).
Proof.
move => eN mN; split => h; last by apply:csum_of_even.
by ex_middle h'; move: (proj2(csum_of_even_odd eN (conj mN h'))).
Qed.

Lemma csum_of_oddP n m: oddp n -> natp m  ->
  (evenp (n +c m) <-> oddp m).
Proof.
move => on mN; split => h; last by apply:csum_of_odd.
case: (p_or_not_p (evenp m)) => // h'.
by move: (proj2(csum_of_even_odd h' on)); rewrite csumC.
Qed.

Definition cdouble n := \2c *c n.
Definition chalf n := n  %/c \2c.


Lemma cdoubleE n : cdouble n = n +c n.
Proof. by rewrite csum_nn. Qed.


Lemma NS_double n: natp n -> natp (cdouble n).
Proof. move => h; apply: (NS_prod NS2 h). Qed.

Lemma NS_half n: natp n -> natp (chalf n).
Proof. by apply:(NS_quo). Qed.


Lemma cdouble0: cdouble \0c = \0c.
Proof. by rewrite /cdouble cprod0r. Qed.

Lemma even_double n: natp n -> evenp (cdouble n).
Proof. 
move => h; split; first by apply: NS_double.
exact: (proj33 (cdivides_pr1 h NS2)). 
Qed.

Lemma odd_succ_double n: natp n -> oddp (csucc (cdouble n)).
Proof. by move => /even_double/succ_of_even. Qed.

Lemma half_even n: evenp n -> n = cdouble (chalf n).
Proof. move => [nN pb]; move: (cdiv_pr nN NS2); rewrite pb csum0r; fprops. Qed.

Lemma half_odd n: oddp n -> n = csucc (cdouble (chalf n)).
Proof. 
move/oddp_alt => [nN on].
move: (cdiv_pr nN NS2). 
by rewrite on Nsucc_rw //; apply: NS_double; apply:NS_half.
Qed.

Lemma cdouble_halfV n: natp n ->
   n = cdouble (chalf n) \/ n = csucc (cdouble (chalf n)).
Proof.
move => nN; case:(p_or_not_p (evenp n)) => h. 
  by left; exact: (half_even h).
right; exact: (half_odd (conj nN h)).
Qed.

Lemma even_half n: natp n -> chalf (cdouble n) = n.
Proof. move => nN; exact (cdivides_pr4 NS2 nN card2_nz). Qed.

Lemma odd_half n: natp n -> chalf (csucc (cdouble n)) = n.
Proof.
move=> nN; move:(NS_double nN) => n2N.
have h: cdivision_prop (csucc (cdouble n)) \2c n \1c. 
   split; [ by rewrite (Nsucc_rw n2N) | exact: clt_12].
symmetry; exact: (proj1 (cquorem_pr (NS_succ n2N)  NS2 nN NS1 h)).
Qed.

Lemma half0: chalf \0c = \0c.
Proof. by rewrite -{1} cdouble0(even_half NS0). Qed.

Lemma half1: chalf \1c = \0c.
Proof. by rewrite - succ_zero  -{1} cdouble0 (odd_half NS0). Qed.

Lemma half2: chalf \2c = \1c.
Proof. by rewrite - (cprod1r CS2)  (even_half NS1). Qed.

Lemma double_sum a b: cdouble a +c cdouble b = cdouble (a +c b).
Proof. by rewrite /cdouble cprodDr. Qed.

Lemma double_prod a b:  a *c cdouble b = cdouble (a *c b).
Proof. by rewrite /cdouble cprodA cprodA (cprodC a). Qed.

Lemma double_succ a: natp a -> cdouble (csucc a) = csucc (csucc (cdouble a)).
Proof.
move => aN; move:(NS_double aN) => dN.
rewrite (Nsucc_rw aN) - double_sum {2} /cdouble (cprod1r CS2) - csum_11.
by rewrite csumA -(Nsucc_rw dN) - (Nsucc_rw (NS_succ dN)).
Qed.

Lemma cdouble_pow2 n: natp n -> cdouble(\2c ^c n) = \2c ^c (csucc n).
Proof. by move => h;rewrite (cpow_succ _ h) cprodC. Qed.

Lemma half_succ n : natp n -> chalf (csucc (csucc n)) = csucc (chalf n).
Proof.
move => nN; move: (NS_half nN) => hN; move: (NS_succ hN) => shN.
case: (cdouble_halfV nN) => ->; rewrite - (double_succ hN).
  by rewrite ! even_half.
by rewrite ! odd_half.
Qed.

Lemma double_inj a b: natp a -> natp b ->  cdouble a = cdouble b -> a = b.
Proof. by move => aN bN; move/(cprod_eq2l NS2 aN bN card2_nz). Qed.

Lemma double_monotone a b: natp a -> natp b -> 
   (cdouble a <=c cdouble b <-> a <=c b).
Proof.
move => pa pb; rewrite /cdouble.
split; [apply:(cprod_le2l NS2 pa pb card2_nz) | apply: cprod_Meqle].
Qed.

Lemma double_monotone2 a b: natp a -> natp b -> 
  (cdouble a <c cdouble b <-> a <c b).
Proof.
move => aN bN; split.
  move => [/(double_monotone aN bN) sa sb]; split => // h; case: sb; ue.
move =>[/(double_monotone aN bN) sa sb]; split => //.
by move /(double_inj aN bN).
Qed.

Lemma double_monotone3 a b: natp a -> natp b -> 
   (csucc (cdouble a) <c cdouble b <-> a <c b).
Proof.
move => aN bN. 
move:(cleSltP (NS_succ (NS_double aN)) (cdouble b)); rewrite -(double_succ aN).
move:(iff_trans (double_monotone (NS_succ aN) bN) (cleSltP aN b)).
move => ha hb; exact (iff_trans (iff_sym hb) ha).
Qed.


Lemma half_monotone n m: natp n -> natp m -> n <=c m ->
  chalf n <=c chalf m.
Proof.
move => nN mN.
move:(NS_half nN) (NS_half mN) => hnN hmN.
case: (cdouble_halfV nN)  => {1} ->;case: (cdouble_halfV mN)  => {1} ->.
+ by move/(double_monotone hnN hmN).
+ move/(cltSleP (NS_succ (NS_double hmN))); rewrite - (double_succ hmN).
  by move/(double_monotone2 hnN (NS_succ hmN)); move/(cltSleP hmN).
+ by move/(cleT (cleS (NS_double hnN))) /(double_monotone hnN hmN).
+ move/(cleSSP (CS_nat(NS_double hnN)) (CS_nat (NS_double hmN))).
  by move/(double_monotone hnN hmN).
Qed.

Lemma half_monotone2 n m: natp n -> natp m ->
  n <=c (chalf m) -> cdouble n <=c m.
Proof.
move => nN mN; move /(double_monotone nN (NS_half mN)) => sa.
case: (cdouble_halfV mN) => -> //.
exact:(cleT sa (cleS (NS_double (NS_half mN)))).
Qed.

Lemma double_le_odd1 p k: natp k -> natp p -> 
    cdouble p <=c csucc (cdouble k) ->  p <=c k.
Proof.
move => kN pN le1; case:(NleT_el pN kN) => // /(cleSltP kN).
move/(double_monotone (NS_succ kN) pN);rewrite (double_succ kN) => le2.
case: (cleNgt le2 (cle_ltT le1 (cltS (NS_succ (NS_double kN))))).
Qed.

Lemma double_le_odd2 p k: natp k -> natp p -> 
  csucc (cdouble k) <=c cdouble p -> csucc k <=c p.
Proof.
move => kN pN; move/cleSS. 
rewrite - (double_succ kN); apply:(double_le_odd1 pN (NS_succ kN)).
Qed.

Lemma cle_n_doublen n: natp n -> n <=c cdouble n.
Proof.
move => nN.
rewrite cdoubleE; apply:(Nsum_M0le _ nN).
Qed.

Lemma cle_Sn_doublen n: natp n -> n <> \0c -> csucc n <=c cdouble n.
Proof.
move => nN /(cpred_pr nN)  [sa ->].
rewrite (double_succ sa);apply: cleSS; apply: cleSS; apply:(cle_n_doublen sa).
Qed.

Lemma clt_n_doublen n: natp n -> n <> \0c -> n <c cdouble n.
Proof. by move => nN /(cle_Sn_doublen nN) /(cleSltP nN). Qed.

Lemma cle_halfn_n n: natp n -> chalf n <=c n.
Proof.
move => nN.
have H:=(cle_n_doublen (NS_half nN)).
case:(cdouble_halfV nN); move => {2} -> //.
apply: (cleT H (cleS (NS_double (NS_half nN)))).
Qed.

Lemma cle_halfSn_n n: natp n -> chalf (csucc n) <=c n.
Proof.
move => nN.
case: (equal_or_not n \0c) => nz.
  rewrite nz succ_zero half1; fprops.
move:(cpred_pr nN nz) => [sa sb]; rewrite sb (half_succ sa).
by move/(cleSSP (CS_nat (NS_half sa)) (CS_nat sa)): (cle_halfn_n sa).
Qed.


Lemma double_nz n: natp n -> n <> \0c -> 
    (cdouble n <> \0c /\ cdouble n <> \1c).
Proof.
move => nN nz; split; first by apply: (cprod2_nz card2_nz nz).
by move => h; move:(proj2 (odd_one)) (even_double nN); rewrite -/(cdouble n) h.
Qed.

Lemma doubleS_nz n: natp n -> n <> \0c -> 
    (csucc (cdouble n) <> \0c /\ csucc (cdouble n) <> \1c).
Proof.
move => nN nz; split; first by apply: succ_nz.
rewrite - succ_zero; move/(csucc_inj (CS_nat (NS_double nN)) CS0).
apply: (cprod2_nz card2_nz nz).
Qed.

Lemma even_odd_dichot n (m := csucc n): natp n ->
  [\/ m = \1c, 
      (m = cdouble (chalf m) /\ chalf m <=c n) |
      [/\  m = csucc (cdouble (chalf m)), (chalf m) <=c n &
          csucc (chalf m) <=c n]].
Proof.
move => nN; rewrite /m.
have mN:= NS_succ nN.
have hN:= NS_half mN.
have aa:=(cle_halfSn_n nN).
case: (equal_or_not n \0c) => nz; first by constructor 1; rewrite nz succ_zero.
case: (cdouble_halfV mN) => mv; first by constructor 2. 
constructor 3; split => //; apply/(cleSltP hN). 
apply/(double_monotone2 hN nN) /(cleSltP (NS_double hN)). 
by rewrite - mv; apply:(cle_Sn_doublen nN nz).
Qed.

Lemma fusc_induction (p: property):
   p \0c -> p \1c -> (forall k, natp k -> p k -> p (cdouble k)) ->
   (forall k, natp k -> p k -> p (csucc k) -> p (csucc (cdouble k))) ->
  forall n, natp n -> p n.
Proof.
move => p0 p1 pe po.
have Hr:(forall n, natp n -> (forall k, k<=c n -> p k) -> p (csucc n)).
  move => n nN Hrec; move:(NS_half (NS_succ nN)) => hN.
  case:(even_odd_dichot nN).
  + by move => ->.
  + by move => [sa sb]; rewrite sa; apply: (pe _ hN); apply: (Hrec _ sb).
  + by move => [sa sb sc]; rewrite sa; apply: (po _ hN); apply: Hrec.
apply: Nat_induction1 => n nN h.
case: (equal_or_not n \0c) => nz; first by rewrite nz.
move: (cpred_pr nN nz) =>[sa sb]; rewrite  sb; apply: (Hr _ sa).
by move => k/(cltSleP sa); rewrite - sb; apply: h.
Qed.



Lemma split_sum_even_odd (F: fterm) n:
  natp n -> n <> \0c ->
  csumb (Nintc n) F =
  csumb (Nintc (chalf n)) (fun k => F (cdouble k))
  +c csumb (Nintc (chalf (cpred n))) (fun k => F (csucc (cdouble k))).
Proof.
move => nN nz.
set A := Zo (Nintc n) evenp.
set B := Zo (Nintc n) oddp.
have pa: disjoint A B by apply:disjoint_pr => u /Zo_hi eu /Zo_hi [_].
have -> : Nintc n = A \cup B.
  set_extens t; last by move/setU2_P; case => /Zo_S.
  case:(p_or_not_p (evenp t)) => et ta; first by apply: setU2_1; apply:Zo_i.
  apply: setU2_2; apply:Zo_i => //; split => //; apply: (Nint_S ta).
move:(NS_half nN) => hN.
move: (cpred_pr nN nz) => [pN pv].
move:(NS_half pN) => hpN.
rewrite (csumA_setU2 _ pa); apply: f_equal2;apply:csum_Cn2; split.
+ move => x /(NintcP hN) xle; move:(NS_le_nat xle hN) => xN.
  apply/Zo_P; split; last by apply:even_double. 
  by apply/(NintcP nN); apply:half_monotone2.
+ by move => x y /Nint_S xN /Nint_S yN; move/(double_inj xN yN).
+ move => y /Zo_P[yi ye]; move:(half_even ye) => he; exists (chalf y) => //.
  by apply /(NintcP hN); move/(NintcP nN): yi => /(half_monotone (proj1 ye) nN).
+ move => x /(NintcP hpN) xle; move:(NS_le_nat xle hpN) => xN.
  apply/Zo_P; split; last by apply:odd_succ_double. 
  apply/(NintcP nN); rewrite pv. 
  by apply/(cleSSP (CS_nat (NS_double xN)) (CS_nat pN));apply: half_monotone2. 
+ move => x y /Nint_S xN /Nint_S yN.
  have ha: (cardinalp (cdouble x)) by rewrite /cdouble; fprops.
  have hb: (cardinalp (cdouble y)) by  rewrite /cdouble; fprops.
  by move/ (csucc_inj ha hb) /(double_inj xN yN).
+ move => y /Zo_P[yi yo]; move:(half_odd yo) => he; exists (chalf y) => //.
  apply /(NintcP hpN); move/(NintcP nN): yi.
  have ha: (cardinalp (cdouble(chalf y))) by rewrite /cdouble; fprops.
  have hb: cardinalp (cdouble (chalf (cpred n))) by rewrite /cdouble; fprops.
  have hyN := (NS_half (proj1 yo)).
  have hc: cardinalp (csucc (cdouble (chalf (cpred n)))) by apply: CS_succ.
   rewrite {1} pv {1} he;case: (cdouble_halfV pN) => eq; rewrite {1} eq.
    move/(cleSSP ha hb) => h. 
    by apply/(double_monotone hyN hpN).
  have hf:natp (csucc (cdouble (chalf (cpred n)))) by rewrite -eq.
  move/(cleSSP ha hc); move/(cltSleP hf); rewrite - (double_succ hpN). 
  by move/(double_monotone2 hyN (NS_succ hpN))/(cltSleP hpN).
Qed.

Lemma split_sum_even_odd_alt (F: fterm) n:
  natp n -> 
  csumb (Nint n) F =
  csumb (Nint (chalf (csucc n))) (fun k => F (cdouble k))
  +c csumb (Nint (chalf n)) (fun k => F (csucc (cdouble k))).
Proof.
move => nN.
case: (equal_or_not n \0c) => nz.
  rewrite nz succ_zero half0 half1 Nint_co00. 
  rewrite /csumb !csum_trivial; aw; trivial;rewrite  csum0r; fprops.
case: (equal_or_not n \1c) => no.
  rewrite no succ_one half1 half2 Nint_co00 /csumb (proj2 Nint_co01).
  set F1 := Lg _ _; set F2 := Lg _ _.
  have ha: (domain F1 =  singleton \0c) by rewrite /F1; aw.
  have hb: (domain F2 =  singleton \0c) by rewrite /F2; aw.
  have hc:= (set1_1 \0c).
  rewrite (csum_trivial1 ha) (csum_trivial1 hb) /F1 /F2 !LgV//.
  rewrite cdouble0 csum_trivial; aw; trivial; rewrite csum0r; fprops.
move: (cpred_pr nN nz) => [sa sb].
have h: (cpred n) <> \0c by move => h; case no; rewrite sb h succ_zero.
move:(cpred_pr sa h) => [sa' sb'].
move:(split_sum_even_odd F sa h).
rewrite  (Nint_co_cc sa)(Nint_co_cc ((NS_half sa'))).
rewrite (Nint_co_cc (NS_half sa)) -(half_succ sa)  -(half_succ sa'). 
by rewrite - sb' - sb.
Qed.

(** base two log *)

Definition clog2 n := least_ordinal (fun z => n <c \2c ^c z) n. 

Lemma clog0 : clog2 \0c = \0c.
Proof.
rewrite /clog2.
set p := (fun z => \0c <c \2c ^c z).
have h: p \0c by rewrite /p cpowx0; apply: clt_01.
by move:(least_ordinal1 OS0 h) => [_ _ hc]; move: (hc _ OS0 h) => /sub_set0 ->.
Qed.

Lemma clog_nz n (m := clog2 n): natp n -> n <> \0c ->
   [/\ natp m, m <> \0c, \2c ^c (cpred m) <=c n & n <c \2c ^c m].
Proof.
move => nN nz; move: (CS_nat nN) => cn.
rewrite /m /clog2; set p := (fun z => n <c \2c ^c z); clear m.
have pn: p n by apply: (cantor cn).
move: (least_ordinal4 (OS_cardinal cn) pn); set m:= (least_ordinal p n).
move => [sa sb sc].
move:(sc _ (OS_cardinal cn) pn) => le1. 
have mN: natp m.
  apply /(oltP OS_omega);  move/(oltP OS_omega):nN => h; exact:ole_ltT le1 h.
case: (equal_or_not m \0c) => mz.
  by case:nz; move: sb; rewrite /p mz cpowx0 => /clt1.
move: (cpred_pr mN mz) => [ha hb].
split => //; case: (NleT_el (NS_pow NS2 ha) nN) => // lt2.
move: (cpred_lt mN mz) => /oclt lt3.
case:(oltNge lt3 (sc _ (proj31_1 lt3) lt2)).
Qed.

Lemma clog_pr n m: natp n -> natp m -> 
    \2c ^c m <=c n -> n <c \2c ^c (csucc m) -> clog2 n = csucc m.
Proof.
move => nN mN eq1 eq2.
case: (equal_or_not n \0c) => nz.
  by move: eq1; rewrite nz => /cle0 =>/ (cpow_nz card2_nz).
move:(clog_nz nN nz) => [lN lz eq3 eq4].
move:(cle_ltT eq1 eq4)  =>  /(cpow2_MeqltP mN lN) /(cleSltP mN); apply:cleA.
move:(cpred_pr lN lz) => [sc sd]. 
move:(cle_ltT eq3 eq2) =>  /(cpow2_MeqltP sc (NS_succ mN)) /(cleSltP sc); ue.
Qed.

Lemma clog_double n: natp n -> n <> \0c -> clog2 (cdouble n) = csucc (clog2 n).
Proof.
move => nN nz.
move:(clog_nz nN nz) => [sa sb sc sd]; apply:(clog_pr (NS_double nN) sa).
  move: (cpred_pr sa sb) => [ha ->]; rewrite - (cdouble_pow2 ha).
  by apply/(double_monotone (NS_pow NS2 ha) nN).
by rewrite - (cdouble_pow2 sa); apply /(double_monotone2 nN (NS_pow NS2 sa)).
Qed.

Lemma clog_succ_double n: natp n ->
    clog2 (csucc (cdouble n)) = csucc (clog2 n).
Proof.
move => nN.
case: (equal_or_not n \0c) => nz.
   rewrite nz /cdouble clog0 cprod0r {1} succ_zero; apply:(clog_pr NS1 NS0).
     rewrite cpowx0; fprops.
  rewrite succ_zero;apply: (cantor CS1).
move:(clog_nz nN nz) => [sa sb sc sd]. 
apply:(clog_pr (NS_succ (NS_double nN)) sa).
  move: (cpred_pr sa sb) => [ha ->]; rewrite - (cdouble_pow2 ha).
  apply: cleT (cleS (NS_double nN)).
  by apply/(double_monotone (NS_pow NS2 ha) nN).
by rewrite - (cdouble_pow2 sa); apply /(double_monotone3 nN (NS_pow NS2 sa)).
Qed.

Lemma clog1 : clog2 \1c = \1c.
Proof. 
rewrite - {2} succ_zero;apply: (clog_pr NS1 NS0). 
  rewrite cpowx0; fprops.
rewrite succ_zero (cpowx1 CS2); apply: clt_12.
Qed.

Lemma NS_log n: natp n -> natp (clog2 n).
Proof.
move => nN; case: (equal_or_not n \0c) => nz; first by rewrite nz clog0; fprops.
by move:(clog_nz nN nz) => [].
Qed. 

Lemma power2_log_even n: natp n -> n <> \0c -> evenp (\2c ^c  (clog2 n)).
Proof.
move => nN nz; move:(clog_nz nN nz) => [sa sb sc sd].
move:(cpred_pr sa sb) => [ha hb]; rewrite hb - (cdouble_pow2 ha).
by apply: (even_double (NS_pow NS2 ha)).
Qed.
 
Lemma log2_pow n: natp n -> clog2 (\2c ^c n) = (csucc n).
Proof.
move => nN; move: (NS_pow NS2 nN) => pN.
apply:(clog_pr pN nN (proj33 (NleR pN))). 
apply/(cpow2_MeqltP nN (NS_succ nN)); apply/(cltS nN).
Qed.

Definition base_two_reverse n :=
   let F := the_expansion \2c n in 
   let p := cardinal (domain F) in 
   expansion_value (Lg p (fun z => (Vg F (p -c (csucc z))))) \2c. 

Lemma base2r_zero: base_two_reverse \0c = \0c.
Proof. 
rewrite / base_two_reverse (the_expansion_zero NS2 clt_12).
by rewrite domain_set0 cardinal_set0; apply: csum_trivial; aw.
Qed.

Lemma base2r_one: base_two_reverse \1c = \1c.
Proof. 
rewrite / base_two_reverse (the_expansion_digit NS2 clt_12 card1_nz clt_12).
move: (simple_fct2 \0c \1c)  => [_ sb _ _ h].
rewrite sb cardinal_set1 /expansion_value Lgd csum_trivial3 h cpowx0.
have zz: inc \0c (singleton \0c) by fprops.
rewrite !LgV //; first by rewrite  (cprod1r CS1) (card_card CS1).
rewrite succ_zero cdiff_nn; fprops.
Qed.

Lemma base2_expansion_prop n (F:= the_expansion \2c n)
    (p := cardinal (domain F)) : natp n -> n <> \0c -> 
    [/\ expansion_of F \2c p n, p <> \0c &  Vg F (cpred p) = \1c].
Proof.
move => nN nz.
move: (the_expansion_pr NS2 clt_12 nN); rewrite -/F -/p; move => [ha hb].
case: (equal_or_not p \0c) => pz.
  case: nz; move: ha => [hc <-]; apply: csum_trivial; aw.
  by apply:card_nonempty.
split => //; case: hb => // [] [_ hb].
move:ha => [[_ pN _ [pb pc pd]] pe].
suff: inc (cpred p) (domain F) by move => /pd/clt2[].
rewrite pc; apply /(NltP pN); apply: (cpred_lt pN pz).
Qed.

Lemma log2_pr1 n (k := \2c ^c (cpred (clog2 n))) : natp n -> n <> \0c ->
  n = k +c (n %%c k).
Proof.
move => nN nz.
move:(clog_nz nN nz) => [sa sb]; rewrite /k.
move: (cpred_pr sa sb) => []; set m := cpred (clog2 n).
move => mN mv sc sd. 
move: (cdivision nN (NS_pow NS2 mN) (@cpow2_nz m)) => [qN rN Ha].
move/(cdivision_prop_alt nN (NS_pow NS2 mN)  qN rN (@cpow2_nz m)):(Ha).
move: Ha => [nv rs] [hu hv _].
case: (equal_or_not (n %/c \2c ^c m) \0c) => qnz.
  by move: (cle_ltT sc hv); rewrite qnz succ_zero (cprod1r (proj31 sc)); case. 
move:(cle_ltT hu sd); rewrite mv - (cdouble_pow2 mN) cprodC. 
move/(cprod_lt2r (NS_pow NS2 mN) qN  NS2) /clt2; case => // eq1.
move: nv; rewrite eq1 cprod1r//; fprops.
Qed.


Lemma log2_pr2 n : natp n -> 
   clog2 n = cardinal (domain (the_expansion \2c n)).
Proof.
move => nN.
case: (equal_or_not n \0c) => nz.
  by rewrite nz (the_expansion_zero NS2 clt_12) clog0 domain_set0 cardinal_set0.
move:(base2_expansion_prop nN nz). 
set c := cardinal _; move => [[sa sb] cz sd].
move: (sa) => [_ cN _ _].
move: (cpred_pr cN cz) => [se sf]. 
move: (expansion_prop9 sa); rewrite sb sf;apply: (clog_pr nN se).
rewrite sf in sa.
have ca: cardinalp (\2c ^c cpred c) by fprops.
rewrite - sb (expansion_prop7 sa (CS_nat se)) sd (cprod1l ca).
by apply: csum_Mle0. 
Qed.

Lemma base2r_even n: natp n -> 
  base_two_reverse (cdouble n) = base_two_reverse n.
Proof.
move => nN.
have dN:= (NS_double nN).
case: (equal_or_not n \0c) => nz; first by rewrite nz cdouble0.
move:(base2_expansion_prop nN nz).
move:(base2_expansion_prop dN (cprod2_nz card2_nz nz)).
rewrite /base_two_reverse.
set E1 := (the_expansion \2c n).
set E2 := (the_expansion \2c (cdouble n)).
set p1:= (cardinal (domain E1)); set p2 := (cardinal (domain E2)).
move => [[sa sb] hb hc] [[sc sd] hf hg].
move: (expansion_prop8_rev sc NS0 clt_02)=> [].
set E3 := Lg _ _.
rewrite sd (csum0r (CS_prod2 _ _)) cprodC -/(cdouble n) => qa qb.
have qc: (expansion_normal_of E2 \2c p2 (cdouble n)).
  split  => //; right; split => //; rewrite hc; fprops.
have p1N: natp p1 by case: sc.
have qd: (expansion_normal_of E3 \2c (csucc p1) (cdouble n)).
  split => //; right; split => //; first by apply:succ_nz. 
  have p1i: inc p1 (csucc p1) by apply: Nsucc_i. 
  rewrite (cpred_pr2 p1N) /E3 LgV // (variant_false _ _  hf) hg; fprops.
move:(expansion_unique1 qc qd)=> [qe qf].
have zi: inc \0c (csucc p1) by apply/(NleP p1N); apply:(cle0n p1N).
have p1i: inc p1 (csucc p1) by apply/(NleP p1N); fprops.
have qg: Vg E2 \0c = \0c by rewrite qe /E3 LgV//; aw;trivial;Ytac0.
have cp1:= CS_nat p1N.
have ns1: natp (csucc p1) by apply: NS_succ.
have hh: expansion (Lg (csucc p1) (fun z => Vg E2 (csucc p1 -c csucc z)))
   \2c (csucc p1).
  move: sa => [q1 q2 q3 [q4 q5 q6]]; split => //; split; aww.
  move => i ii; rewrite LgV//; apply: q6; rewrite q5 qf (cdiff_pr6 p1N).
  apply/(NleP p1N);apply: (cdiff_le1 _ cp1).
  exact:(NS_inc_nat ns1 ii).  
rewrite qf (expansion_prop7 hh cp1) (LgV p1i) cdiff_nn qg cprod0l.
rewrite csum0r; last by rewrite /expansion_value /csumb; fprops.
rewrite /expansion_value /restr !Lgd;apply:csumb_exten.
move => i ii /=.
have iN:= NS_inc_nat p1N ii.
move/(NltP p1N): (ii) => lip.
have sip1: csucc i <=c p1 by  apply/(cleSltP iN).
have ha: inc (p1 -c i) (csucc p1). 
  apply/(NleP p1N);apply: (cdiff_le1 _ cp1).
have isp: inc i (csucc p1) by rewrite (succ_of_nat p1N); apply:setU1_r.
rewrite !LgV //  (cdiff_pr6 p1N iN) qe - (cdiff_A1 p1N iN sip1) /E3 LgV //.
by rewrite (variant_false _ _ (cdiff_nz lip)).
Qed.

Lemma base2r_odd n: natp n -> 
  base_two_reverse (csucc (cdouble n)) = \2c ^c (clog2 n) +c base_two_reverse n.
Proof.
move => nN.
have dN:= (NS_double nN).
case: (equal_or_not n \0c) => nz. 
  rewrite nz cdouble0 succ_zero base2r_one base2r_zero clog0.
  by rewrite cpowx0 (csum0r CS1).
move:(base2_expansion_prop nN nz).
move:(base2_expansion_prop (NS_succ dN) (@succ_nz _)).
rewrite /base_two_reverse.
set E1 := (the_expansion \2c n).
set E2 := (the_expansion \2c (csucc (cdouble n))).
set p1:= (cardinal (domain E1)); set p2 := (cardinal (domain E2)).
move => [[sa sb] hb hc] [[sc sd] hf hg].
move: (expansion_prop8_rev sc NS1 clt_12)=> [].
set E3 := Lg _ _.
rewrite sd cprodC -/(cdouble n) - (Nsucc_rw dN) => qa qb.
have qc: (expansion_normal_of E2 \2c p2 (csucc (cdouble n))).
  split  => //; right; split => //; rewrite hc; fprops.
have p1N: natp p1 by case: sc.
have qd: (expansion_normal_of E3 \2c (csucc p1) (csucc (cdouble n))).
  split => //; right; split => //; first by apply:succ_nz. 
  have p1i: inc p1 (csucc p1) by apply: Nsucc_i. 
  rewrite (cpred_pr2 p1N) /E3 LgV // (variant_false _ _ hf)hg; fprops.
have [qe qf]:=(expansion_unique1 qc qd).
have zi: inc \0c (csucc p1)  by apply/(NleP p1N); apply:(cle0n p1N).
have p1i: inc p1 (csucc p1) by apply/(NleP p1N); fprops.
have qg: Vg E2 \0c = \1c by rewrite qe /E3 LgV//; aw;trivial;Ytac0.
have cp1:= CS_nat p1N.
have ns1:=(NS_succ p1N).
have hh: expansion (Lg (csucc p1) (fun z => Vg E2 (csucc p1 -c csucc z)))
   \2c (csucc p1).
  move: sa => [q1 q2 q3 [q4 q5 q6]]; split => //; split; aww.
  move => i ii; rewrite LgV//; apply: q6; rewrite q5.
  rewrite qf (cdiff_pr6 p1N  (NS_inc_nat ns1 ii)). 
  apply/(NleP p1N);apply: (cdiff_le1 _ cp1). 
rewrite qf (expansion_prop7 hh cp1) (LgV p1i) cdiff_nn qg csumC.
rewrite (cprod1l (CS_pow _ _)) (log2_pr2 nN); apply:f_equal.
rewrite /expansion_value /csumb; apply: f_equal; aw.
apply:Lg_exten => // i ii.
have iN:=  NS_inc_nat p1N ii.
move/(NltP p1N): (ii) => lip.
have sip1: csucc i <=c p1 by  apply/(cleSltP iN).
have ha: inc (p1 -c i) (csucc p1). 
  apply/(NleP p1N);apply: (cdiff_le1 _ cp1).
have isp: inc i (csucc p1) by rewrite (succ_of_nat p1N); apply:setU1_r.
rewrite !LgV//  (cdiff_pr6 p1N iN) qe - (cdiff_A1 p1N iN sip1) /E3 LgV//.
by rewrite (variant_false _ _ (cdiff_nz lip)).
Qed.
  
Lemma NS_reverse n: natp n -> natp (base_two_reverse n).
Proof.
move: n; apply: fusc_induction.
+ rewrite base2r_zero; fprops.
+ rewrite base2r_one; fprops.
+ by move => k kn; rewrite base2r_even.
+ move => k kn sa _; rewrite ( base2r_odd kn); apply:NS_sum sa. 
  apply:(NS_pow NS2 (NS_log kn)).
Qed.

Lemma base2r_oddp n: natp n -> n <> \0c -> oddp (base_two_reverse n).
Proof.
move: n; apply: fusc_induction.
+ by case.
+ rewrite base2r_one => _; apply: odd_one.
+ move => k kN H ck. 
  by rewrite (base2r_even kN); apply: H => h; case:ck; rewrite h cdouble0.
+ move =>k kN Ha _ ck.
  rewrite (base2r_odd kN).
  case: (equal_or_not k \0c) => knz.
      rewrite knz clog0 base2r_zero cpowx0 (csum0r CS1); apply: odd_one.
  apply: (csum_of_even_odd (power2_log_even kN knz) (Ha knz)).
Qed.

Lemma base2r_oddK n (r := base_two_reverse) :
  oddp n -> r (r n) = n.
Proof.
move => [nN nen]; move:(NS_half nN) => hN; case: (cdouble_halfV nN) => eq.
   case: nen; rewrite eq; apply: (even_double hN). 
have nz: n <> \0c by rewrite eq; apply: succ_nz.
have ox:=(base2r_oddp nN nz).
move: (erefl (r n)); pose x := r n; rewrite - {1 3} /x /r.
have xn: natp x by apply: NS_reverse.
case: (equal_or_not x \0c) => xz.
  by case: (proj2 ox); rewrite -/r - /x xz; apply: even_zero.
rewrite /base_two_reverse.
move:(base2_expansion_prop nN nz) (base2_expansion_prop xn xz).
set Fn := (the_expansion \2c n); set Fx := (the_expansion \2c x).
set pn := cardinal (domain Fn); set px := (cardinal (domain Fx)).
set Gn := Lg _ _; set Gx := Lg _ _. 
move => [[pa pb] pc pd]  [[qa qb] qc qd] eq1. 
move:(pa) => [ha hb hc [hd he hf]].
have hi: expansion Gn \2c pn.
   split => //; rewrite /Gn; split; aww => i iI; rewrite LgV//.
   move/(NltP hb): iI => ra; move:(NS_lt_nat ra hb) => iN.
   have rb: csucc i <=c pn by apply /cleSltP.
   apply: hf; rewrite he;apply /(NltP hb).
   apply:(cdiff_Mlt hb hb rb); apply:(csum_M0lt hb (@succ_nz _)).
have Ha:(expansion_normal_of Fx \2c px  x).
  split => //; right; split => //; rewrite qd; fprops.
have Hb:(expansion_normal_of Gn \2c pn  x).
  have pp:inc (cpred pn) pn by apply /(NltP hb); apply: cpred_lt.
  have pq: expansion_of Gn \2c pn x by split; [ | symmetry].
  split => //;right; split => //;rewrite /Gn LgV//.
  rewrite - (proj2 (cpred_pr hb pc)) cdiff_nn => bad.
  have [sa sb]:=(cpred_pr hb pc).
  move: pb; rewrite /expansion_value he sb.
  set t := csumb _ _ => eq2.
  suff: evenp t by move => eq3; case: nen; rewrite - eq2.
  have : forall i, i<=c (cpred pn) -> natp (Vg Fn i).
     move => i /(cltSleP sa); rewrite - sb => /(NltP hb).
    rewrite - he; move=> /hf => h; apply: (NS_lt_nat h NS2).
  rewrite /t; move: (cpred pn) sa; apply: Nat_induction.
    rewrite succ_zero csum_trivial3 bad (cprod0l).
    rewrite (card_card CS0); move => _; apply: even_zero.
  move => jk kN Hrec aux; rewrite (induction_on_sum _ (NS_succ kN)).
  have hw:(forall i, i <=c jk -> natp (Vg Fn i)). 
    by move => i ij; apply: aux; apply: (cleT ij (cleS kN)).
  apply: (csum_of_even (Hrec hw)); rewrite - (cdouble_pow2 kN) double_prod.
  apply: even_double; apply: NS_prod; [ apply: aux; fprops | fprops ].
have [eq2 eq3] := (expansion_unique1 Ha Hb).
rewrite - pb /expansion_value /Gx Lgd eq3 he eq2 /Gn.
apply: csumb_exten => i iI.
move/(NltP hb):(iI) => ra;have ra1:= (proj1 ra).
have iN:=(NS_lt_nat ra hb).
have rb: csucc i <=c pn by apply /cleSltP.
have rc: pn -c csucc i <c pn.
   apply:(cdiff_Mlt hb hb rb); apply:(csum_M0lt hb (@succ_nz _)).
have rd: inc (pn -c csucc i) pn by apply  /(NltP hb).
by rewrite !LgV // - (csucc_diff hb iN rb) double_diff.
Qed.

Lemma base2r_oddK_bis n (r := base_two_reverse) :
  natp n -> r (r (r n))  = r n.
Proof.
move => nN.
case: (equal_or_not n \0c) => nz; first by rewrite nz /r !base2r_zero.
by apply:base2r_oddK; apply: base2r_oddp.
Qed.

Lemma div3_props: [/\ \0c %%c \3c = \0c, \1c %%c \3c = \1c& \2c %%c \3c = \2c]. 
Proof.
have ha := NS3. 
have hb:= (cltS NS2).
have hc:= (clt_ltT clt_12 hb).
have hd:= (clt_ltT clt_01 hc).
by split; symmetry;apply:crem_small.
Qed.

Lemma div3_props2: \3c %%c \3c = \0c /\ \4c %%c \3c = \1c. 
Proof.
move: (cdivides_itself NS3) div3_props => [_ _ ha] [_ hb _].
split => //.
move: (crem_sum NS3 card3_nz NS3 NS1).
by rewrite /eqmod ha hb (csum0l CS1) hb -(Nsucc_rw NS3).
Qed.

Lemma div3_vals n (m := n %%c \3c): natp n ->
   [\/ m = \0c, m = \1c | m = \2c].
Proof.
move => nN.
move: (cdivision nN NS3 card3_nz) => []; rewrite -/m => _ mN [_ m3].
case: (equal_or_not m \2c) => m2; first by constructor 3.
move /(cltSleP NS2): m3 => l2; case: (clt2 (conj l2 m2)) => h; in_TP4.
Qed.

Lemma double_mod3 n: natp n ->
  (n %%c \3c = \0c <-> (cdouble n) %%c \3c = \0c).
Proof.
have [sa sb sc]:=div3_props.
move => nN.
move: (crem_prod NS3 card3_nz NS2 nN); rewrite sc => H.
split => hb; first by move: H; rewrite /eqmod hb cprod0r sa.
move: H; rewrite /eqmod -/(cdouble n) hb; case: (div3_vals nN) => // ->.
  by rewrite (cprod1r CS2) sc => h; case: card2_nz.
by rewrite cprod_22 (proj2 div3_props2) => h ; case: card1_nz.
Qed.

Lemma cmodmod n p: natp n -> natp p -> p <> \0c ->  n %%c p = n %c[mod p].
Proof.
move => nN pN pnz; move: (cdivision nN pN pnz) => [qN rN [pa pb]].
have dp: (cdivision_prop (n %%c p) p \0c (n %%c p)).
  by  split => //; rewrite cprod0r (Nsum0l rN).
by rewrite - (proj2 (cquorem_pr rN pN NS0 rN dp)).
Qed.

Lemma cmodmod3 n: natp n  ->  n %%c \3c = n %c[mod \3c].
Proof. move => nN; apply:(cmodmod nN NS3 card3_nz). Qed.

Lemma cmodmod2 n: natp n  -> n %%c \2c = n %c[mod \2c].
Proof. move => nN; apply:(cmodmod nN NS2 card2_nz). Qed.


(* Fibonacci *)


Definition Fib2_rec :=
 induction_term  (fun _ v => (J (Q v) (P v +c Q v))) (J \0c \1c).

Definition Fib n := P (Fib2_rec n).

Lemma Fib_rec n : natp n -> Fib (csucc (csucc n)) = Fib n +c Fib (csucc n).
Proof. 
move => nN; rewrite /Fib/Fib2_rec (induction_terms _ _ (NS_succ nN)). 
by rewrite pr1_pair (induction_terms _ _ nN); aw.
Qed.

Lemma Fib0: Fib \0c = \0c.
Proof. by rewrite /Fib /Fib2_rec induction_term0; aw. Qed.

Lemma Fib1: Fib \1c = \1c.
Proof.
rewrite /Fib/Fib2_rec - succ_zero (induction_terms _ _ NS0) induction_term0.
by aw.
Qed.

Lemma Fib2: Fib \2c = \1c.
Proof. 
rewrite - succ_one - succ_zero (Fib_rec NS0) succ_zero. 
by rewrite Fib0 Fib1 (csum0l CS1).
Qed.

Lemma Fib3: Fib \3c = \2c.
Proof. 
rewrite /card_three - succ_one (Fib_rec NS1) succ_one. 
by rewrite Fib1 Fib2 csum_11.
Qed.

Lemma NS_Fib n: natp n -> natp (Fib n).
Proof.
move => nN; suff: natp (Fib n) /\ natp (Fib (csucc n)) by case.
move: n nN; apply: Nat_induction.
   rewrite succ_zero Fib0 Fib1; fprops.
move => n nN [sa sb]; split => //; rewrite (Fib_rec nN); fprops.
Qed.

Hint Resolve NS_Fib : fprops.

Lemma Fib_gt0 n: natp n -> n <> \0c ->  (Fib n) <> \0c.
Proof.
move => nN nz; move:(cpred_pr nN nz) => [sa ->].
move: (cpred n) sa; clear n nN nz; apply: Nat_induction. 
   rewrite succ_zero Fib1; fprops.
by move => n nN Hr; rewrite (Fib_rec nN); move/csum_nz => [_].
Qed.

Lemma Fib_smonotone n m: natp n -> natp m -> n <> \0c -> n <> \1c -> 
   n <c m -> Fib n <c Fib m.
Proof.
move => nN mN nz no.
case: (equal_or_not m \0c) => mz; first by rewrite mz; move/clt0.
move:(cpred_pr mN mz) => [sa ->]; move/(cltSleP sa).
move: (cpred m) sa; clear m mN mz; apply:Nat_induction.
  move => /cle0 ->;rewrite succ_zero Fib0 Fib1; apply: clt_01.
move => m mN Hrec; rewrite (Fib_rec mN) csumC.
case: (equal_or_not n (csucc m)) => eq1 h.
  rewrite - eq1; apply: (csum_M0lt (NS_Fib nN)); apply:(Fib_gt0 mN) => mz.
  by case: no; rewrite eq1 mz succ_zero.
move: (Nsum_M0le (Fib m) (NS_Fib (NS_succ mN))).
by apply:clt_leT; apply: Hrec; apply /(cltSleP mN).
Qed.

Lemma Fib_monotone n m: natp n -> natp m -> n <=c m -> Fib n <=c Fib m.
Proof.
move => nN mN le; move:(CS_nat (NS_Fib mN)) => h.
case:(equal_or_not n m) => eq; first by rewrite eq; apply: (cleR h).
case:(equal_or_not n \0c) => eq2; first by rewrite eq2 Fib0; apply: cle0x.
case:(equal_or_not n \1c) => eq3.
  move: le; rewrite eq3 Fib1 => hh; apply:(cge1 h); apply:(Fib_gt0 mN) => mz.
  apply: (cleNgt hh); rewrite mz; fprops. 
exact (proj1(Fib_smonotone nN mN eq2 eq3 (conj le eq))).
Qed.

Lemma Fib_gt1 n: natp n -> \2c <c n -> \1c <c Fib n.
Proof.
move => nN h.
by move:(Fib_smonotone NS2 nN card2_nz (nesym card_12) h); rewrite Fib2.
Qed.

Lemma Fib_eq1 n: natp n -> (Fib n = \1c <-> (n = \1c \/ n = \2c)).
Proof.
move => nN; split; last by case => ->; rewrite ?Fib1 ?Fib2.
move => eq1.
case: (NleT_ell nN NS2); first by right.
  case /clt2; [move => ne0; move: eq1; rewrite ne0 Fib0; fprops| by left].
by move/(Fib_gt1 nN); rewrite eq1; case.
Qed.

Lemma Fib_eq n m: natp n -> natp m -> 
  (Fib n = Fib m <-> [\/ n = m, (n = \1c /\ m = \2c) |(n = \2c /\ m = \1c) ]).
Proof.
move => nN mN; split; last first.
  by case; first (by move ->); move => [-> ->]; rewrite Fib1 Fib2.
wlog : n m nN mN / n <=c m => H.
  case: (NleT_ee nN mN); [by apply:H | move => le eq].
  case: (H _ _ mN nN le (sym_eq eq)).
  + by constructor 1.
  + by move => [sa sb]; constructor 3.
  + by move => [sa sb]; constructor 2.
case: (equal_or_not n m) => enm eq; first by constructor 1.
case: (equal_or_not n \0c) => nz.
  by rewrite nz in enm; move:(Fib_gt0 mN (nesym enm));rewrite - eq nz Fib0;case.
case: (equal_or_not n \1c) => n1.
  case: (equal_or_not \2c m) => m2; first by constructor 2.
  have: \2c <c m. 
    by split => //; rewrite - succ_one; apply/(cleSltP NS1); rewrite - n1.    
  by move/(Fib_gt1 mN); rewrite - eq n1 Fib1; case.
by case: (proj2(Fib_smonotone nN mN nz n1 (conj H enm))).
Qed.

Lemma Fib_add n m: natp n -> natp m ->
  Fib (csucc (n +c m)) =
  (Fib n) *c (Fib m) +c (Fib (csucc n)) *c (Fib (csucc m)).
Proof.
move => nn;move: n nn m; apply: Nat_induction.
   move => m mN; move:(CS_nat (NS_Fib (NS_succ mN))) => cf.
   by rewrite (Nsum0l mN) succ_zero Fib0 Fib1 cprod0l (cprod1l cf) csum0l.
move => n nN Hrec m mN.
case: (equal_or_not m \0c) => mz.
  move:(CS_nat (NS_Fib (NS_succ (NS_succ nN)))) => cf.
  rewrite mz succ_zero Fib0 Fib1 cprod0r (cprod1r cf) (csum0l cf) csum0r;fprops.
move:(cpred_pr mN mz) => [sa sb].
rewrite (csum_Sn _ nN) (Fib_rec (NS_sum nN mN)) (Fib_rec nN) (Hrec _ mN).
rewrite cprodDl csumA csumA {1} sb (csum_nS _ sa) (Hrec _ sa) - sb.
apply:f_equal2; last by reflexivity.
rewrite csumC csumA (csumC (_ *c _)).  
by rewrite - cprodDr {2} sb - (Fib_rec sa) - sb csumC.
Qed.

Lemma Fib_sub n m: natp n -> natp m -> m <=c n->
  Fib (n -c m) = Yo (evenp m)
    (Fib n *c Fib (csucc m) -c Fib (csucc n) *c Fib m)
    (Fib (csucc n) *c Fib m -c Fib n *c Fib (csucc m)).
Proof.
move: even_zero => ez.
move => nN; move: n nN m; apply: Nat_induction. 
  move=> m mN /cle0 ->; rewrite (Y_true ez) Fib0 cprod0r cprod0l.
  by rewrite cdiff_nn Fib0.
move => n nN Hrec m mN; case: (equal_or_not m \0c) => mz.
  move:(NS_succ nN) => ha; move:(NS_Fib ha) => hb.
  rewrite mz (Y_true ez) succ_zero Fib0 Fib1 cprod0r.
  by rewrite (cdiff_n0 ha) (cprod1r (CS_nat hb)) (cdiff_n0 hb).
move:(cpred_pr mN mz); set c := cpred m; move => [cN cv].
rewrite cv (cdiff_pr6 nN cN); move /(cleSSP (CS_nat cN) (CS_nat nN)) => h.
move: (NS_Fib cN)(NS_Fib nN)(NS_Fib (NS_succ cN))(NS_Fib (NS_succ nN)).
move => qa qb qc qd.
rewrite (Hrec _ cN h) (Fib_rec cN) (Fib_rec nN) cprodDr cprodDl.
Ytac ec; first rewrite (Y_false (proj2 (succ_of_even ec))) cdiff_pr5; fprops.
rewrite (Y_true (succ_of_odd (conj cN ec))) cdiff_pr5; fprops. 
Qed.

Lemma Fib_odd n (square := fun a => a *c a): natp n ->
  Fib (csucc (cdouble n)) = square (Fib n) +c square (Fib (csucc n)).
Proof. by move => nN; rewrite cdoubleE  (Fib_add nN nN).  Qed.

Lemma Fib_even n: natp n ->
  Fib (cdouble (csucc n)) = Fib (csucc n) *c (cdouble (Fib n) +c Fib (csucc n)).
Proof. 
move => nN. 
rewrite (double_succ nN)  cdoubleE - (csum_nS _ nN).
rewrite (Fib_add nN (NS_succ nN)) cprodC - cprodDr (Fib_rec nN).
by rewrite csumA - cdoubleE.
Qed.

Lemma Fib_add3  n: natp n -> 
    Fib (n +c \3c) = Fib n +c cdouble (Fib (csucc n)).
Proof.
move => nN. 
rewrite (csum_nS _ NS2) (Fib_add nN NS2) Fib3 Fib2.
by rewrite (Nprod1r (NS_Fib nN)) cprodC.
Qed.

Lemma Fib_div n m: n %|c m -> Fib n %|c Fib m.
Proof.
move => h;rewrite(cdivides_pr h).
move:h => [mN nN _]; move:(NS_quo n mN); set k := (m %/c n).
case: (equal_or_not n \0c) => nz.
   rewrite nz  cprod0l Fib0 => _; apply: (cdivides_zero NS0).
move:(cpred_pr nN nz) => [sN sv].
move:(k); apply: {m mN k} Nat_induction. 
  rewrite cprod0r Fib0; exact (cdivides_zero  (NS_Fib nN)).
move => m mN Hrec.
have ha:= (cdivides_trans2 (NS_Fib sN) Hrec).
have hb: Fib n %|c (Fib (csucc (n *c m)) *c Fib n).
  rewrite cprodC;apply:cdivides_pr1; apply:NS_Fib; fprops.
rewrite (cprod_nS _ mN) {3}sv (csum_nS _ sN) (Fib_add (NS_prod nN mN) sN) - sv.
exact (proj1 (cdivides_sum ha hb)).
Qed.

Lemma Fib_is_even_mod3 n: natp n -> 
   (evenp (Fib n) <-> \3c %|c n).
Proof.
have H: forall m, natp m -> evenp (Fib (\3c *c m)).
  move => m mN.
  by move:(Fib_div (cdivides_pr1 mN NS3)); rewrite Fib3; move => [sa _ sb].
have aux: forall k, natp k -> csucc (csucc k) = k +c \2c.
  move => k kN. 
  by rewrite - csum_11 csumA (Nsucc_rw (NS_succ kN)) (Nsucc_rw).
suff H1:forall n, natp n ->
  oddp (Fib (csucc (\3c *c n))) /\ oddp (Fib (csucc (csucc (\3c *c n)))).
  move => nN;split; last first.
    by move/cdivides_pr => ->; apply: H; apply: NS_quo.
  move: NS3  => n3 ef.
  move:(cdivision nN n3 card3_nz) => [sa sb [sc sd]]; split => //.
  have ha := (NS_prod n3 sa).
  move: (H1 _ sa); rewrite (aux _ ha) (Nsucc_rw ha); move => [[_ eqa] [_ eqb]].
  by case: (div3_vals nN) => //eq1; move: ef; rewrite sc eq1.
apply: {n} Nat_induction.
   rewrite cprod0r succ_zero succ_one Fib2 Fib1;split; apply odd_one.
move => n nN [_ Hrec]; move:(NS_succ nN) => sN.
have hc: natp (\3c *c n +c \2c) by apply: (NS_sum (NS_prod NS3 nN) NS2).
have ha:=  NS_prod NS3 sN.
suff hb: oddp (Fib (csucc (\3c *c csucc n))).
  rewrite (Fib_rec ha); split => //; exact:(csum_of_even_odd (H _ sN) hb).
rewrite (cprod_nS _ nN) {2} /card_three (csum_nS _ NS2) (Fib_rec hc).
rewrite csumC  - (csum_nS _ NS2) -/card_three - (cprod_nS _ nN).
by rewrite - {1} (aux _ (NS_prod NS3 nN)); apply:(csum_of_even_odd (H _ sN)).
Qed.

Definition composite n := 
  exists a, [/\ natp a, \1c <c a, a <c n & a %|c n].

Lemma composite_prod a b: natp a -> natp b -> \1c <c a -> \1c <c b ->
   composite (a *c b).
Proof.
move => aN bN h1 h2.
move/(strict_pos_P1 aN): (clt_ltT clt_01 h1) => anz.
by exists a;split  => //; [apply:cprod_M1lt | apply: cdivides_pr1].
Qed.

Lemma composite_prod_rev n: natp n -> composite n ->
   exists a b, [/\  natp a, natp b, \1c <c a, \1c <c b & n = a *c b].
Proof.
move => nN  [a [aN pa pb pc]]; exists a,(n %/c a).
move:(cdivides_pr pc) (NS_quo a nN) => eq qN; rewrite - eq; split => //;split.
  rewrite - succ_zero; apply /(cleSltP NS0); split; first exact:(cle0n qN).
  move => qz.
  by case:(proj2 (clt_ltT clt_01 (clt_ltT pa pb))); rewrite eq - qz cprod0r.
by move => eq1;move: (proj2 pb);rewrite eq - eq1 (cprod1r (CS_nat aN)).
Qed.


Lemma composite_even_fib n: natp n -> \2c <c n -> 
  composite (Fib (cdouble n)).
Proof.
move => nN n2; case: (equal_or_not n \0c) => nz.
  by case:(proj2 (clt_ltT clt_02 n2)).
move:(nN) n2;move: (cpred_pr nN nz) => [sa ->] sN n2.
have ha:= NS_Fib sN.
have hb:= NS_Fib sa.
have hc:= (NS_sum (NS_double hb) ha).
have hd := (Fib_gt1 sN n2).
rewrite (Fib_even sa); apply:(composite_prod ha hc hd).
apply: (clt_leT hd); apply:(Nsum_Mle0 _ ha).
Qed.


Lemma composite_fib n: natp n -> n <> \4c -> 
  composite n -> composite (Fib n).
Proof.
move => nN n4 [a [aN a1 an dvd]].
case: (equal_or_not \2c a) => ea2.
  move: an n4.
  move:(cdivides_pr dvd); rewrite - ea2 -/(double _) -/(chalf _) => -> an n4.
  have kN:= (NS_half nN).
  apply: (composite_even_fib kN); split.
    case: (NleT_el NS2 kN) => // /clt2; case => eq;
    move:an; rewrite eq ?cprod0r ? (cprod1r CS2) => hh; first case: (clt0 hh).
    by case: (proj2 hh).
  by move => e1; case: n4; rewrite - e1 cprod_22.
have a2: \2c <c a by split => //;rewrite - succ_one; apply /(cleSltP NS1).
have anz:=  (nesym (proj2 (clt_ltT clt_01 a1))).
exists (Fib a); split => //.
+ by apply: NS_Fib.
+ apply: (Fib_gt1 aN a2).
+ apply: (Fib_smonotone aN nN anz (nesym (proj2 a1)) an). 
+ exact(Fib_div dvd).
Qed.

Definition coprime a b :=
  [/\ natp a, natp b & forall x, x %|c a -> x %|c  b -> x = \1c].

Lemma coprime_S a b: coprime a b -> coprime b a.
Proof. by move => [ha hb hc]; split => // x xb xa; apply: hc. Qed.

Lemma cdivides_oner x: x %|c \1c -> x = \1c.
Proof.
move => xp;move/cdivides_pr: (xp) => /esym p1.
by case:(cprod_eq1 (CS_nat (proj32 xp)) (CS_nat (NS_quo x NS1)) p1).
Qed.


Lemma coprime_1n a : natp a -> coprime \1c a.
Proof.
by move: NS1 => ns1 h; split => //x xp _; apply:cdivides_oner.
Qed.
  
Lemma coprime_sump a b k: natp k ->  coprime a b ->
   coprime a (b +c (a *c k)).
Proof.
move => kN [aN bN cp].
have ha:= (NS_prod aN kN); have hb := NS_sum bN ha.
split => // => x xda xds; apply:cp => //. 
rewrite csumC in xds.
by have hc:= (cdivides_trans2 kN xda); move:(cdivides_diff1 bN hc xds).
Qed.

Lemma coprime_sum a b: coprime a b ->  coprime a (b +c a).
Proof.
move => h;  move:(h) => [aN bN _].
rewrite -{2}(cprod1r (CS_nat aN)); apply:(coprime_sump NS1 h).
Qed.


Lemma coprime_diff a b: natp b -> coprime a (b +c a) -> coprime a b.
Proof.
move => bN [aN baN h]; split => // x xa xc.
exact:(h _ xa (proj1 (cdivides_sum xc xa))).
Qed.

Lemma coprime_bezout1 a b: natp a -> natp b ->
  (exists u v, [/\ natp u, natp v & a *c u = \1c +c b *c v]) ->
  coprime a b.
Proof.
move => aN bN [u [v [uN vN eq1]]]; split => // x xda xdb.
move:(cdivides_trans2 uN xda); rewrite eq1 csumC => xdc.
move: (cdivides_diff1 NS1 (cdivides_trans2 vN xdb) xdc).
apply:cdivides_oner.
Qed.

Lemma coprime_bezout2 a b: coprime a b ->
  (a = \0c /\ b = \1c) \/
  exists u v, [/\ natp u, natp v & a *c u = \1c +c b *c v].
Proof.                                              
move=> h.
move:(cleR (CS_sum2 a b)).  
move:(NS_sum (proj31 h)(proj32 h)).
move: {1 3}(a+cb) => n nN; move: n nN a b h; apply:Nat_induction.
  move => a b [aN bN cab] /cle0 /csum_nz [az bz].
  set H := cdivides_zero NS0.
  by rewrite az bz in cab;move: (card1_nz(esym (cab \0c H H))).
move => N nN Hrec a b cab /cle_eqVlt; case => ll; last first.
   by move/(cltSleP nN): ll => ll; apply: Hrec.
move:(cab) => [aN bN _].
case: (NleT_ee aN bN) => leab.
   move: (cdiff_pr leab); move: (NS_diff a bN); set c := _ -c _ => cN bv.
   case: (equal_or_not a \0c) => anz.
    left; split => //; move:(proj33 cab); rewrite anz => h.
    by move: (h b (cdivides_zero bN) (cdivides_itself bN)).
  right.
  move: cab; rewrite - bv csumC => /(coprime_diff cN) => cac.
  have ll1: a +c c <=c N.
    by apply/(cltSleP nN); rewrite - ll bv csumC;apply:csum_M0lt.
  case: (Hrec _ _ cac ll1); first by case.
  move => [u [v [un vN bz]]]; exists (v+c u), v; split;[ fprops | done | ].
  by rewrite cprodDl csumA - bz csumC cprodDr.
move: (cdiff_pr leab); move: (NS_diff b aN); set c := _ -c _ => cN av.
right;case: (equal_or_not b \0c) => bnz.
   move:(proj33 cab); rewrite bnz => h.
   rewrite (h a (cdivides_itself aN) (cdivides_zero aN)).
   exists \1c,\0c; split; [apply: NS1 | apply: NS0 | ].
   by rewrite (cprod1r CS1) cprod0r (csum0r CS1).
have ll1: c +c b <=c N.
  by apply/(cltSleP nN); rewrite csumC - ll av; apply:csum_M0lt.
move: cab; rewrite -av csumC => /coprime_S/(coprime_diff cN)/coprime_S => cac.
case: (Hrec _ _ cac ll1).
   move => [-> ->]; exists \1c,\0c; split; [exact NS1 | exact NS0 |].
  by rewrite (csum0l CS1) (cprod1l CS1)  cprod0r (csum0r CS1) .
move => [u [v [un vN bz]]]; exists u, (v +c u); split;[ done |fprops | ].
by rewrite cprodDr csumA - bz cprodDl.
Qed.

Lemma coprime3 a b c: coprime a b -> natp c -> a %|c (c *c b) -> a %|c c.
Proof.
move => cab cN dd; move: (cab) => [aN bN _].
move:(cdivides_pr dd). move:(NS_quo a (NS_prod cN bN)).  
set s := _ %/c _ => sN aav.
case: (coprime_bezout2 cab).
  by move => [az bo]; move:dd; rewrite bo (cprod1r (CS_nat cN)).
move => [u [v [uN vN bz]]].
move:(cdivides_pr1 (NS_prod uN cN) aN); rewrite cprodA bz cprodDl.
rewrite (cprod1l (CS_nat cN)) cprodC  cprodA aav - cprodA csumC => h.
exact: (cdivides_diff1 cN (cdivides_pr1 (NS_prod sN vN) aN) h).
Qed.
  
Lemma coprime_Sn_fib n: natp n -> coprime (Fib n) (Fib (csucc n)).
Proof.
move:n; apply: Nat_induction.
  rewrite succ_zero  Fib0 Fib1; apply: coprime_S; apply:(coprime_1n NS0).
by move => n nN /coprime_S Hrec;rewrite (Fib_rec nN); apply:coprime_sum.
Qed.

Lemma coprime_example p q: coprime p q ->
   (p -c \1c) *c (q -c \1c) = cdouble(csumb q (fun k => (k *c p) %/c q)).
Proof.
move => cpq.
have H s: natp s -> \0c %/c s = \0c by move/cdivision_of_zero; case.
case: (equal_or_not q \0c) => qz.
  by rewrite qz (cdiff_wrong cle_01) cprod0r csum_trivial0 cdouble0.
case: (equal_or_not q \1c) => qo.
   rewrite qo cdiff_nn cprod0r csum_trivial3 cprod0l.
   by rewrite(H _ NS1) cardinal_set0 cdouble0.
move:(cpq) => [pN qN _].
move:(cge2 (CS_nat qN) qz qo) => qge2.
move:(cdiff_pr qge2) (NS_diff \2c qN); set q2 := _ -c _ => q2v q2N.
have q1N := NS_succ q2N. 
have q2v': q = csucc (csucc q2).
  by rewrite (Nsucc_rw q1N)  (Nsucc_rw q2N)-  csumA csum_11 csumC -  q2v.
pose f i := ((csucc i) *c p) %/c q.
set X := csumb _ _.
have ->: X = csumb (csucc q2) f.
  rewrite /X {1}q2v' (fct_sum_rec1 _ q1N) cprod0l(H _ qN) csum0r //.
  apply:CS_cardinal.
rewrite cdoubleE {1} (fct_sum_rev f q2N) sum_of_sums.
rewrite q2v' -(cpred_pr4 (CS_succ _)) (cpred_pr2 q1N) - csum_of_same. 
apply:csumb_exten => i /(NltP q1N) /(cltSleP q2N) lin /=; rewrite /f.
have iN:=(NS_le_nat lin q2N).
have ha: natp (csucc (q2 -c i) *c p) by fprops.
have hb: natp (csucc i *c p) by fprops.
move: (cdivision ha qN qz)  (cdivision hb qN qz).
set A := _ %/c _; set B := _ %/c _; set r1 := _ %%c _; set r2 := _ %%c _.
move => [AN r1N [div1 lt1]] [BN r2N [div2 lt2]].
have: q *c p =  csucc (q2 -c i) *c p +c csucc i *c p. 
  rewrite -  cprodDl (csum_Sn _ (NS_diff i q2N)) (csum_nS _ iN) csumC.
 by rewrite (cdiff_pr lin) q2v'.
have ABN:= NS_sum AN BN.
rewrite div1 div2 csumACA - cprodDr => hc.
move:(cdivides_pr1 pN qN) (cdivides_pr1 ABN qN);rewrite hc => d1 d2.
move: (cdivides_pr (cdivides_diff1 (NS_sum r1N r2N) d2 d1)) => eq3.
move:(csum_Mlelt  qN (proj1 lt1) lt2); rewrite eq3 csum_nn cprodC.
move/(cprod_lt2r qN (NS_quo q (NS_sum r1N r2N)) NS2) => /clt2; case => eq4.
  move: eq3; rewrite eq4 cprod0r => /csum_nz [_ r2z].
  move:(cdivides_pr1 BN qN);rewrite -(csum0r (CS_prod2 q B)) - r2z -div2 => dd.
  move:(cdivides_pr (coprime3 (coprime_S cpq) (NS_succ iN) dd)).
  move:(NS_quo q (NS_succ iN)); set C := _ %/c _ => cN eq2.
  case: (equal_or_not C \0c) => cz.  
    by move:(@succ_nz i); rewrite eq2 cz cprod0r.
  move:(cltS q1N).
  move:(cprod_Meqle q (cge1 (CS_nat cN) cz)).
  rewrite (cprod1r (CS_nat qN)) - eq2 q2v' => ra.
  case: (cltNge (clt_leT (cltS q1N) ra)).
  by move /(cleSSP (CS_nat iN) (CS_nat q2N)): lin.
move: hc; rewrite eq3 eq4 - cprodDr.
move/(cprod_eq2l qN pN (NS_sum ABN NS1) qz) => ->; exact:(cdiff_pr1 ABN NS1).
Qed.


(* summation prpoepties for Fib *)

Section FibP1.

Definition fib_list L :=
 [/\ fgraph L, natp  (domain L) & sub (range L) C2].        
Definition fib_listA L :=
  fib_list L /\
  forall i, natp i -> inc (csucc i) (domain L) ->
        Vg L i = C0 \/ Vg L (csucc i) = C0.
Definition fib_listB L :=
  fib_listA L /\ (domain L = emptyset \/ Vg L (cpred (domain L)) = C0).
Definition fib_list_plus L x :=
   L +s1 (J (domain L) x). 


Definition fib_listsA :=
   Zo (fgraphs Nat C2) fib_listA.
Definition fib_listsB :=
   Zo (fgraphs Nat C2) fib_listB.
  
Lemma fiblistsAP x: inc x fib_listsA <-> fib_listA x.
Proof.
split; first  by move/Zo_hi.
move => h; apply: Zo_i => //; apply/ fgraphsP.
by move: h => [[qa qb qc] _]; split => // t;  apply: NS_inc_nat.
Qed.

Lemma fiblistsBP x: inc x fib_listsB <-> fib_listB x.
Proof.
split; first  by move/Zo_hi.
move => h; apply: Zo_i => //; apply/ fgraphsP.
by move: h => [[[qa qb qc] _] _]; split => // t;  apply: NS_inc_nat.
Qed.


Lemma fiblist_p1 L x: fib_list L -> inc x (domain L) ->
  Vg L x = C0  \/ Vg L x = C1.                                     
Proof.
move =>[qa qb qc] xdl.
have vr : inc (Vg L x) (range L) by apply/(range_gP qa); ex_tac.
by move:(qc _ vr) => /set2_P.
Qed.

Lemma fiblist_add_x L x: fib_list L -> inc x C2 -> 
  fib_list (fib_list_plus L x). 
Proof.
move => [qa qb qc] xd.
have nn: ~ inc (domain L) (domain L) by apply: Nat_decent.
have dd: domain (fib_list_plus L x) = csucc (domain L).
  rewrite domain_setU1 succ_of_nat //.
have ff: fgraph (fib_list_plus L x) by apply: fgraph_setU1.
split.
+ done.
+ by rewrite dd; apply: NS_succ.
+ move => t /(range_gP ff); rewrite domain_setU1 => - [u ua ->].
  case/setU1_P: ua => ua.
    rewrite setU1_V_in //; apply: qc; apply/(range_gP qa); ex_tac.
  by rewrite ua setU1_V_out.
Qed.


Lemma fiblist_add_0 L: fib_listA L -> fib_listB (fib_list_plus L C0). 
Proof.
move => [ha hb].
have icc: inc C0 C2 by fprops.
move: (ha) =>[qa qb qc].
have nn: ~ inc (domain L) (domain L) by apply: Nat_decent.
have dd: domain (fib_list_plus L C0) = csucc (domain L).
  rewrite domain_setU1 succ_of_nat //.
move: (fiblist_add_x ha icc) => hc; split => //; last first.
   right; rewrite dd (cpred_pr1 (CS_nat qb)) setU1_V_out //.
split => // i iN; rewrite domain_setU1; case /setU1_P; last first.
  by move ->; right;rewrite setU1_V_out.
move => h.
have idl: inc i (domain L).
  by apply/(NltP qb); apply /(cleSltP iN); move/(NltP qb): h; case.
by rewrite ! setU1_V_in //; apply: hb.
Qed.


Lemma fiblist_add_1 L: fib_listB L -> fib_listA (fib_list_plus L C1). 
Proof.
move => [[ha hb] hc].
have icc: inc C1 C2 by fprops.
move: (fiblist_add_x ha icc) => hd; split => //.
move: ha =>[qa qb qc].
have nn: ~ inc (domain L) (domain L) by apply: Nat_decent.
move => i iN;  rewrite domain_setU1; case /setU1_P => h; last first.
  left; case: hc; rewrite - h; first by move:(@succ_nz i).
  by rewrite (cpred_pr1 (CS_nat iN)) setU1_V_in // - h; apply: Nsucc_i.
have idl: inc i (domain L).
  by apply/(NltP qb); apply /(cleSltP iN); move/(NltP qb): h; case.
by rewrite ! setU1_V_in //; apply: hb.
Qed.

Lemma fiblist_sub L n (M := restr L n) :
  fib_listA L -> natp n -> domain L = csucc n ->
  [/\ fib_listA M,  domain M =  n & fib_listB L \/ fib_listB M].
Proof.
move => [[qa qb qc] qd] nN da.
have fgg: fgraph (restr L n) by fprops.
have ra: domain M = n by rewrite /M restr_d.
have rb: fib_listA M.
  rewrite /M; split; first saw.
    move => t/(range_gP fgg); aw => - [i  ii]; bw => // ->.
    apply: qc; apply/(range_gP qa); exists i => //.
    by rewrite da; apply/(NleP nN); case /(NltP nN): ii.
  aw; move => i iN iin.
  move/(NltP nN): (iin) => lin.
  have ni: inc i n. apply/(NltP nN); exact : (cle_ltT (cleS iN) lin).
  have rc: inc (csucc i) (domain L) by  rewrite da; apply/(NleP nN); case: lin.
  bw => //;apply: qd => //.
split => //.
rewrite/  fib_listB ra da (cpred_pr1 (CS_nat nN)).
case: (equal_or_not  (Vg L n) C0) => rd; first by left; split => //; right.
right; split => //; case: (equal_or_not n \0c) => nz; [by left | right].
move: (cpred_pr nN nz)  =>[sa sb].
have cnn: inc (cpred n) n by rewrite {2}  sb; apply: Nsucc_i.
have nd: inc (csucc (cpred n)) (domain L) by  rewrite - sb da; apply: Nsucc_i.
move: (qd _ sa nd); rewrite - sb; case => //; rewrite /M; bw => //.
Qed.

  


Definition fib_listsAc n :=
   cardinal (Zo fib_listsA (fun z => domain z = n)). 
Definition fib_listsBc n :=
   cardinal (Zo fib_listsB (fun z => domain z = n)). 

Lemma fiblist_res1 n: natp n ->
  fib_listsAc n = fib_listsBc (csucc n).
Proof.
move => nN; apply/card_eqP.
set E := Zo _ _ ; set  F := Zo _ _.
exists (Lf (fun z => fib_list_plus z C0) E F).
hnf; saw; apply: lf_bijective.
+ move => z /Zo_P [/fiblistsAP qa qb]; apply: Zo_i.
      by apply/fiblistsBP; apply: fiblist_add_0.
   rewrite domain_setU1 qb succ_of_nat //.
+ move =>  u v /Zo_P [/fiblistsAP qa qb] /Zo_P [/fiblistsAP qc qd] sv.
  move: qa qc => [[ra rb rc] _] [[rd re rf] _].
  apply: fgraph_exten => //; first by rewrite qb qd.
  have nn: ~ inc (domain u) (domain u) by apply: Nat_decent.
  have nn': ~ inc (domain v) (domain v)  by apply: Nat_decent.
  move => i idu.
  move: (f_equal (Vg ^~i) sv); rewrite setU1_V_in // setU1_V_in //. 
  by rewrite qd - qb.
- move => y /Zo_P [/fiblistsBP qa qb].
  move: (fiblist_sub  (proj1 qa) nN qb) =>[qc qd _].
  exists (restr y n); first  by  apply: Zo_i => //; apply/fiblistsAP.
  move: qa => [[[ra rb rc] _]].
  rewrite /fib_list_plus; aw; rewrite qb (cpred_pr1 (CS_nat nN)); case.
    by move: (@succ_nz n).
  move =>  vn0.
  have aux: ~ inc n (domain (restr y n)). aw. by apply: Nat_decent.
  have aux2: fgraph (restr y n) by fprops.
  apply: fgraph_exten => //.
  - by apply: fgraph_setU1.
  - by rewrite domain_setU1; aw; rewrite qb succ_of_nat.
  - rewrite qb (succ_of_nat nN) => t /setU1_P; case => h.
      by rewrite setU1_V_in //; bw => //; aw.
    by rewrite h setU1_V_out.
Qed.

Lemma fiblist_res2 n: natp n ->
  fib_listsAc (csucc n) = fib_listsAc n +c fib_listsBc n.
Proof.
rewrite /fib_listsAc /fib_listsBc.
set A := Zo _ _; set B := Zo _ _ ; set C := Zo _ _ => nN.
set B' := Zo fib_listsB (fun z  => domain z = csucc n).
set C' := A -s B'.
have di1: disjoint B' C' by apply: set_I2Cr.
have ->: A = B' \cup C'.
   rewrite setU2_Cr // => t /Zo_P [/fiblistsBP /proj1 qa qb].
   by apply:Zo_i => //; apply /fiblistsAP.
rewrite (csum2_pr5 di1) - csum2cr - csum2cl; apply: f_equal2.
  symmetry; exact:(fiblist_res1 nN).
symmetry;  apply/card_eqP.
exists (Lf (fun z => fib_list_plus z C1) C C').
hnf; saw; apply: lf_bijective.
+ move => z /Zo_P [/fiblistsBP qa qb].
  move: (fiblist_add_1 qa); set r := (fib_list_plus z C1) => ra.
  have dr: domain r = csucc n by  rewrite domain_setU1 qb succ_of_nat.
  apply /setC_P; split; first by  apply: Zo_i => //; apply/fiblistsAP.
  move/Zo_P /proj1/fiblistsBP/proj2; case.
    rewrite dr; apply: succ_nz.
  rewrite dr (cpred_pr1 (CS_nat nN)); rewrite  /r /fib_list_plus qb.
  move: qa => [[[sa sb sc] _] _ ].
  by rewrite setU1_V_out; fprops; rewrite qb; apply: Nat_decent.
+ move =>  u v /Zo_P [/fiblistsBP qa qb] /Zo_P [/fiblistsBP qc qd] sv.
  move: qa qc => [[[ra rb rc] _] _] [[[rd re rf] _] _].
  apply: fgraph_exten => //; first by rewrite qb qd.
  have nn: ~ inc (domain u) (domain u) by apply: Nat_decent.
  have nn': ~ inc (domain v) (domain v)  by apply: Nat_decent.
  move => i idu.
  move: (f_equal (Vg ^~i) sv); rewrite setU1_V_in // setU1_V_in //. 
  by rewrite qd - qb.
- move => y /setC_P [ /Zo_P [/fiblistsAP qa qb]  /Zo_P qc1].
  have nBy: ~ fib_listB y.
    by move => b; case: qc1; split => //; apply/fiblistsBP.
  case: (equal_or_not (Vg y n) C0) =>  qf. 
    case: nBy; split => //.
    by right; rewrite qb (cpred_pr1 (CS_nat nN)).
  move: (fiblist_sub qa nN qb) =>[qc qd]; case => // qe.
  have ndy: inc n (domain y) by  rewrite qb; apply: Nsucc_i.
  case : (fiblist_p1  (proj1 qa) ndy ) => //vn0.
  exists (restr y n); first  by  apply: Zo_i => //; apply/fiblistsBP.
  move: qa => [[ra rb rc] _].
  have aux: ~ inc n n  by apply: Nat_decent.
  have aux2: fgraph (restr y n) by fprops.
  apply: fgraph_exten => //.  
  - by  apply: fgraph_setU1; aw.
  - by rewrite domain_setU1; aw; rewrite qb succ_of_nat. 
  - rewrite qb (succ_of_nat nN) => t /setU1_P; case => h.
      by rewrite setU1_V_in //; bw => //; aw.
    by rewrite /fib_list_plus h; aw; rewrite setU1_V_out; aw.
Qed.


Lemma fiblist_res3:  fib_listsAc \0c = \1c.
Proof.
apply /set_of_card_oneP; apply/singletonP; split.
  exists emptyset; apply:Zo_i; aw; trivial.
  apply/fiblistsAP; split; last by  aw => i _ /in_set0.
  split; [apply: fgraph_set0 | aw; apply: NS0 | rewrite range_set0; fprops].
move => u v /Zo_P [/fiblistsAP [ [qa _ _] _] qb].
move =>  /Zo_P [/fiblistsAP [ [qc _ _] _] qd].
by apply: fgraph_exten => //; try ue; rewrite qb => t /in_set0.
Qed.

Lemma fiblist_res4:  fib_listsBc \0c = \1c.
Proof.
apply /set_of_card_oneP; apply/singletonP; split.
  exists emptyset; apply:Zo_i; aw; trivial.
  apply/fiblistsBP; split; last by aw; left.
  split; last by  aw => i _ /in_set0.
  split; [apply: fgraph_set0 | aw; apply: NS0 | rewrite range_set0; fprops].
move => u v /Zo_P [/fiblistsBP [ [[qa _ _] _] _] qb].
move =>  /Zo_P [/fiblistsBP [ [[qc _ _] _] _] qd].
by apply: fgraph_exten => //; try ue; rewrite qb => t /in_set0.
Qed.

Lemma fiblist_res n:  natp n -> fib_listsAc n = Fib (n +c \2c).
Proof.
move => nN.
suff: fib_listsAc n = Fib (n +c \2c) /\ fib_listsBc n = Fib (n +c \1c).
  by case.
move: n  nN; apply: Nat_induction.
  rewrite fiblist_res3 fiblist_res4 (csum0l CS2) (csum0l CS1).
  by  rewrite Fib1 Fib2.
move => n nN [ha hb];split.
   rewrite - succ_one  (csum_nS _ NS1) - (Nsucc_rw (NS_succ  nN)).
   rewrite (Fib_rec (NS_succ  nN)) csumC fiblist_res2 // ha hb.
   by rewrite - succ_one  (csum_nS _ NS1) - (Nsucc_rw nN).
by rewrite - fiblist_res1 // (csum_Sn _ nN) - (csum_nS _ NS1) succ_one.
Qed.
  

End FibP1.

Section FibP2.

Definition odd_seq s :=
  [/\ fgraph s, natp (domain s) & allf s oddp].
Definition odd_seq_for n s:=
  odd_seq s /\ csum s = n.
Definition odd_seqs n := Zo (fgraphs Nat Nat) (odd_seq_for n).
Definition nb_odd_sums n := cardinal (odd_seqs n).



Lemma odd_seqsP n s: inc s (odd_seqs n) <-> odd_seq_for n s.
Proof.
split; first by   move/Zo_hi. 
move=>h; apply:Zo_i => //.
move: h => [[qa qb qc] qd].
apply/fgraphsP; split => //.
  by move => t  tt; apply: (NS_inc_nat qb tt).
by move => t  /(range_gP qa) [x hb -> ]; move: (qc x hb); case.
Qed.

Lemma nbos_restr s (m:= cpred (domain s)) (r := restr s m):
       domain s <> \0c -> odd_seq s ->
   [/\ odd_seq r, csum s = csum r +c (Vg s m) & oddp (Vg s m)]. 
Proof.
move => ha [hb hc hd].
move: (cpred_pr hc ha); rewrite -/m; move =>[mN mv].
have dd: domain s = m +s1 m by  rewrite mv  (succ_of_nat mN).
split.
- rewrite /r;  split;aww => t; aw => tm; bw => //. apply: hd.
  by rewrite dd;  apply: setU1_r.
- by rewrite (induction_sum1 dd (Nat_decent mN)).
- by apply: hd; rewrite  mv; apply: Nsucc_i.
Qed.

Lemma nbos_p1 s: odd_seq  s -> domain s <=c csum s.
Proof.
move: s.
suff: forall n, natp n -> forall s, domain s = n -> odd_seq s -> n <=c csum s.
  by move => H s sa; apply: (H (domain s)) => //; case: sa.
apply: Nat_induction.
  move => s sa _. rewrite csum_trivial //; fprops.
move => n nN Hrec s sdc sa.
move: (@succ_nz n); rewrite - sdc => dnz.
move: (nbos_restr dnz sa).
set  m := Vg _ _; set r := restr _  _; move => [ra ->  [rb rc]].
have de: domain r = n by  rewrite /r sdc (cpred_pr1 (CS_nat nN)); aw.
move:(Hrec r de ra); rewrite sdc => /cleSS h. apply: (cleT h).
rewrite csucc_pr4; fprops; apply: csum_Meqle.
apply: (cge1 (CS_nat rb)); dneg mm; rewrite mm; apply: even_zero.
Qed.
  

Lemma nbos_p2 n s: natp n -> odd_seq_for n s -> domain s <=c n.
Proof. by move => nN [sa sb]; move: (nbos_p1 sa); ue. Qed.

Lemma nbos0: nb_odd_sums \0c = \1c.
Proof.
apply /set_of_card_oneP; apply/singletonP; split.
  have de: domain emptyset = emptyset by aw.
  exists emptyset; apply/odd_seqsP; split; last  by rewrite csum_trivial.
  split; [apply: fgraph_set0 | rewrite  de; apply: NS0 | ].
  by hnf; rewrite de => t /in_set0.
move =>  u v /odd_seqsP [qa qb] /odd_seqsP [qc qd].
move: (nbos_p1 qa) (nbos_p1 qc); rewrite qb qd => /cle0 du /cle0 dv.
apply: fgraph_exten; [by case: qa | by case qc | by ue | ].
by rewrite du =>  t /in_set0.
Qed.  

Lemma nbos1: nb_odd_sums \1c = \1c.
Proof.
apply /set_of_card_oneP; apply/singletonP; split.
  set f := (Lg C1 (fun z => \1c)).
  have df: domain f = singleton C0 by rewrite /f; aw.
  have vf: Vg f C0 = \1c by  rewrite /f LgV//; apply: set1_1.
  have sf: csum f = \1c by rewrite (csum_trivial1 df) vf (card_card CS1).
  exists f; apply/odd_seqsP; split => //; rewrite /f.
  split; [ fprops | aw; apply:NS1| hnf; aw => t /set1_P ->].
  rewrite vf; apply: odd_one.
move =>  u v /odd_seqsP [qa qb] /odd_seqsP [qc qd].
move: (nbos_p1 qa) (nbos_p1 qc); rewrite qb qd.
case: (equal_or_not (domain u) \0c) => duz.
  by move: qb; rewrite csum_trivial// => h; case:C0_ne_C1.
case: (equal_or_not (domain v) \0c) => dvz.
  by move: qd; rewrite csum_trivial// => h; case:C0_ne_C1.
case/cle_eqVlt; [move => du1 |  by move/clt1].
case/cle_eqVlt; [move => dv1 |  by move/clt1].
move:  qa qc => [ra rb rc] [rd re rf].
have ha: inc \0c  (domain u) by rewrite du1; apply: set1_1.
have hb: inc \0c  (domain v) by rewrite dv1; apply: set1_1.
have duc: cardinalp (Vg u \0c) by  apply: CS_nat; case: (rc C0 ha).
have dvc: cardinalp (Vg v \0c) by  apply: CS_nat; case: (rf C0 hb).
move: qb qd. rewrite (csum_trivial1 du1) (csum_trivial1 dv1).
rewrite ! card_card // => su sv.
apply: fgraph_exten; fprops; try ue.
rewrite du1 => y /set1_P ->; ue.
Qed.


Lemma nbos_rec n: natp n -> n <>  \0c -> 
  nb_odd_sums n = 
  csumb (chalf (csucc n)) (fun i =>(nb_odd_sums (n -c (csucc (cdouble i))))).
Proof.
move => nN nz.
set m := (chalf (csucc n)).
have mN: natp m by  apply: NS_half; apply: NS_succ.
have mp i: inc i m <->  natp i /\ (csucc (cdouble i)) <=c n.
  suff: natp i -> (inc i m <->  csucc (cdouble i) <=c n).
     move => h; split => hyp.
       by move: (NS_inc_nat mN hyp) => iN; split => //; apply/(h iN).
     by move:hyp => [iN hyp]; apply/(h iN).
   move => iN.
   have ha: inc i m <-> csucc i <=c m.
      split; first by move/(NltP mN); move/(cleSltP iN).
      by move/(cleSltP iN); move/(NltP mN).
   apply: (iff_trans ha).
   have dsiN: natp (csucc (cdouble i)) by apply: NS_succ;  apply: NS_double.
   apply: iff_trans (cleSSP (CS_nat dsiN) (CS_nat nN)).
   rewrite - (double_succ iN).
   case: (cdouble_halfV (NS_succ nN)) => ->; rewrite -/m.
     exact: (iff_sym (double_monotone (NS_succ iN) mN)).
   split =>  h.
      move/(double_monotone (NS_succ iN) mN):h => q.
      by apply: (cleT q); apply: cleS; apply: (NS_double mN).
   by apply:(double_le_odd1 mN (NS_succ iN)).
pose lasti i f := Vg f (cpred (domain f)) = i.
pose lastis i := Zo (odd_seqs n) (lasti (csucc (cdouble i))).
pose F := Lg m lastis.
have md: mutually_disjoint F.
   apply: mutually_disjoint_prop; rewrite /F; aw => i j y im jm; bw => //.
   move => /Zo_hi qa /Zo_hi qb.
   move:(NS_inc_nat mN im)(NS_inc_nat mN jm) => iN jN.
   have ci: cardinalp (cdouble i) by  apply: CS_nat; apply: NS_double.
   have cj: cardinalp (cdouble j) by  apply: CS_nat; apply: NS_double.
   by apply: double_inj => //; apply: csucc_inj => //; rewrite - qa - qb.
rewrite /nb_odd_sums.
have ->:  odd_seqs n = unionb F.
  rewrite /F; set_extens t; last first.
    by move/setUb_P; aw; move =>[y ym]; bw => // /Zo_S.
  move => ti; move /odd_seqsP: (ti) => [ost cst].
  case: (equal_or_not (domain t) \0c) => dnz.
    by case:nz; rewrite - cst csum_trivial.
   move: (nbos_restr dnz ost); set r := restr _ _;move => [qa qb qc].  
   move: (half_odd qc); set i := (Vg t (cpred (domain t))) => iv.
   have iN: natp i by  case: qc.
   have hiN: natp (chalf i) by apply: NS_half.
   have him: inc (chalf i) m.
     apply/mp; split => //; rewrite -iv - cst qb; apply: csum_Mle0; fprops.
   by apply /setUb_P; exists (chalf i); aw; bw => //; apply:Zo_i.
rewrite  (csum_pr4 md) /csumb  /F;aw; congr csum; apply: Lg_exten.
move => i im; bw => //.
move/mp: im => [iN le1].
move: (cdiff_pr le1). move: (NS_diff (csucc (cdouble i)) nN).
set p := _ -c _ ; move => pN pv.
apply/card_eqP.
exists (Lf (fun z => restr z (cpred (domain z))) (lastis i) (odd_seqs p)).
pose j := csucc (cdouble i). 
have oj: oddp j.   by apply: odd_succ_double.
saw; apply: lf_bijective.
- move => z /Zo_P [/odd_seqsP [qa qb] qc].
  case: (equal_or_not (domain z) \0c) => duz.
     by case: nz; rewrite - qb csum_trivial.
  move:(nbos_restr duz qa); set r := restr _ _; move =>[ra rb rc].
  apply/odd_seqsP; split => //.
  move: (@NS_in_suml (csum r) (csucc (cdouble i))); rewrite - qc - rb => ww.
  have rra: natp (csum z) by ue.
  have rrb:  cardinalp (csum r) by rewrite /csum; fprops.
  move: qb; rewrite rb qc - pv csumC; apply: csum_eq2l => //.
    by apply: NS_succ; apply: NS_double.
  by apply: ww.
- move =>  u v /Zo_P[ua ub]/Zo_P[va vb] sr.
  move/odd_seqsP: ua =>[[uc1 uc2 uc3] ud].
  move/odd_seqsP: va =>[[vc1 vc2 vc3] vd].
  case: (equal_or_not (domain u) \0c) => duz.
     by case: nz; rewrite - ud csum_trivial.
  case: (equal_or_not (domain v) \0c) => dvz.
     by case: nz; rewrite - vd csum_trivial.
  move: (cpred_pr uc2 duz) (cpred_pr vc2 dvz) => [qa qb][qc qd].
  have dudv: domain u = domain v.
     by rewrite qb qd; move: (f_equal domain sr); aw; move ->.
  apply: fgraph_exten => // t tu.
  move: tu; rewrite qb (succ_of_nat qa) => /setU1_P; case => tt.
      move: (f_equal (Vg ^~ t) sr); bw => //; ue.
  by rewrite tt ub dudv vb.
- move => y /odd_seqsP [qa  qb].
  move: qa => [qa1 qa2 qa3].
  set x := y +s1 (J (domain y)  (csucc (cdouble i))).
  have dx1: domain x = osucc (domain y).
    by rewrite /x; aw; rewrite domain_setU1.
  have dx: domain x = csucc (domain y).
    by  rewrite dx1 succ_of_nat.
  have cpd: (cpred (domain x)) = domain y by rewrite dx cpred_pr1; fprops.
  have ndy: ~ inc (domain y) (domain y) by apply: Nat_decent.
  have qc: lasti (csucc (cdouble i)) x.
    by rewrite /lasti cpd /x setU1_V_out.
  have fgx: fgraph x by  apply: fgraph_setU1.
  have ndx: natp (domain x) by rewrite dx; fprops.
  have axo: allf x oddp.
    move => t; rewrite dx1; case/setU1_P.
      by move => h; rewrite setU1_V_in //; apply: qa3.
     by move ->; rewrite setU1_V_out.
  have rrx:  (restr x (domain y)) = y.
   by apply: fgraph_exten; aww => t tdy; bw => //; rewrite setU1_V_in.
  have xn: inc x (odd_seqs n).
     apply/odd_seqsP; split => //. 
     by rewrite (induction_sum1 dx1) // rrx  - cpd  qc qb csumC  pv.
  exists x; [ apply: Zo_i => // | ue].
Qed. 
  
Lemma nbos_rec_odd n: natp n ->  
  nb_odd_sums (csucc (cdouble n)) = 
  csumb (csucc n) (fun i => nb_odd_sums (cdouble i)).
Proof.
move => nN.
have dN: natp (csucc (cdouble n)) by apply: NS_succ; apply:NS_double.
have dnz: csucc (cdouble n) <> \0c by apply succ_nz.
rewrite (nbos_rec dN dnz) - (double_succ nN) (even_half (NS_succ nN)).
rewrite (fct_sum_rev _ nN) /csumb; congr csum; apply: Lg_exten => i id.
have iN: natp i by  apply: (NS_inc_nat (NS_succ nN) id).
have ddN: natp (cdouble (n -c i)) by  apply: NS_double; apply: NS_diff.
rewrite (cdiff_pr6 (NS_double nN) ddN) ; apply: f_equal.
move/(NleP nN): id => lin.
by rewrite - {1}  (cdiff_pr lin) -(double_sum) cdiff_pr1 //; apply: NS_double.
Qed.



Lemma nbos_rec_even n: natp n ->
  nb_odd_sums (cdouble (csucc n)) = 
  csumb (csucc n) (fun i => nb_odd_sums(csucc (cdouble i))).
Proof.
move => nN.
have dN: natp (cdouble (csucc n)) by apply: NS_double; apply:NS_succ.
have dnz: cdouble (csucc n) <> \0c.
  by rewrite double_succ //; apply succ_nz.
rewrite (nbos_rec dN dnz) (odd_half (NS_succ nN)) (fct_sum_rev _ nN).
rewrite /csumb; congr csum; apply: Lg_exten => i id.
have iN: natp i by apply: (NS_inc_nat (NS_succ nN) id).
have sdnN: natp (csucc (cdouble n)) by apply: NS_succ; apply: NS_double.
have dnN:  natp (cdouble n) by apply: NS_double.
have le1:  n -c i <=c n by apply: (cdiff_le1 _  (CS_nat nN)).
have le2: cdouble (n -c i) <=c cdouble n.
  by apply/(double_monotone (NS_diff i nN) nN). 
have diN: natp (cdouble (n -c i)) by   apply:NS_double; apply: NS_diff.
rewrite (double_succ nN) (cdiff_pr6 sdnN diN) (cdiffSn (NS_double nN) le2).
apply: f_equal; apply: f_equal.
move/(NleP nN): id => lin.
by rewrite - {1}  (cdiff_pr lin) -(double_sum) cdiff_pr1 //; apply: NS_double.
Qed.


Lemma Fib_sums_odd n: natp n ->  
  Fib (csucc (cdouble n)) = 
  csucc (csumb (csucc n) (fun i => Fib (cdouble i))).
Proof.
move: n; apply: Nat_induction.
  rewrite cdouble0 succ_zero csumb1 cdouble0 Fib0 Fib1.
  by rewrite (card_card CS0) succ_zero.
move => n nN Hrec.
have snN:= NS_succ nN.
have sN:  natp (csumb (csucc n) (fun i : Set => Fib (cdouble i))).
   apply: finite_sum_finite; split.
     hnf; aw; move => t tn; bw => //; apply: NS_Fib; apply: NS_double.
     by move: (NS_inc_nat snN tn).
   by aw; apply: finite_set_nat.   
rewrite (csum_fs _ (NS_succ nN)) - (csum_Sn _ sN) - Hrec.
by rewrite (double_succ nN) (Fib_rec (NS_succ (NS_double nN))).
Qed.

Lemma Fib_sums_even n: natp n ->
  Fib (cdouble (csucc n)) = 
  csumb (csucc n) (fun i => Fib(csucc (cdouble i))).
Proof.
move: n; apply: Nat_induction.
  rewrite succ_zero csumb1 cdouble0 succ_zero Fib1 (card_card CS1).
  by rewrite /cdouble (cprod1r CS2) Fib2.
move => n nN Hrec.
rewrite (csum_fs _ (NS_succ nN)) - Hrec.
by rewrite - (Fib_rec (NS_double (NS_succ nN))) (double_succ (NS_succ nN)).
Qed.


Lemma nbos_value n: natp n ->
  nb_odd_sums n = Yo (n  = \0c) \1c (Fib n). 
Proof.
have Ha F N: natp N ->
     csumb (csucc N) F =  (csumb (csucc N -s1 \0c) F) +c (F \0c).
  move => nN; set p := (csucc N -s1 \0c).
  have ha: ~ (inc \0c  p) by case /setC1_P.
  have <-: p +s1 \0c = csucc N by apply: setC1_K; apply/(NleP nN); apply: cle0n.
  by rewrite (csumA_setU1 _ ha).
move => nN; move: (cleR (CS_nat nN)).
move:  n nN {- 2} n; apply: Nat_induction.
  by move => n /cle0 ->; Ytac0; rewrite nbos0.
move => n nN Hrec p le1.
have pN := NS_le_nat le1 (NS_succ nN).
have hN:= NS_half pN.
move: le1; case: (cdouble_halfV pN) => ->.
  move => le1.
  case: (equal_or_not (chalf p) \0c) => hz.
    by rewrite hz cdouble0 nbos0; Ytac0.
  move: (cpred_pr hN hz); set q := cpred _ ; move =>[sa sb].
  rewrite sb { 2} (double_succ sa) (Y_false (@succ_nz _)).
  rewrite (Fib_sums_even sa) (nbos_rec_even sa) /csumb.
  apply: f_equal; apply: Lg_exten => i ilq.
  have iN:=  (NS_inc_nat (NS_succ sa) ilq).
  have le2: csucc (cdouble i) <=c n.
    move: ilq; rewrite - sb => /(NltP hN) /(cleSltP iN).
    move/(double_monotone (NS_succ iN) hN) => h.
    move: (cleT h le1); rewrite double_succ //.     
    by move/(cleSSP (CS_succ _) (CS_nat nN)).
  by rewrite (Hrec _ le2) (Y_false (@succ_nz _)).
have c1: cardinalp (cdouble (chalf p)) by apply: CS_nat; apply: NS_double.
have  c2: cardinalp n  by apply: CS_nat.
move/(cleSSP c1 c2) => le1.
rewrite (Fib_sums_odd hN) (nbos_rec_odd hN).
rewrite (Y_false (@succ_nz _)).
rewrite (Ha _ _ hN) (Ha _ _ hN) cdouble0  nbos0 Fib0.
set s1 := csumb _ _; set s2 := csumb _ _.
have Hb t: inc t (csucc (chalf p)) -> t <> \0c ->
   natp t /\  (nb_odd_sums (cdouble t)) = Fib (cdouble t).
   move => ta tb.
   have tN: natp t by   apply: NS_inc_nat ta; apply: NS_succ.
   split => //.
   have le2: cdouble t <=c n.
    move /(NleP hN): ta => /(double_monotone tN hN) => h;exact: (cleT h le1).
   by rewrite (Hrec _ le2) (Y_false  (proj1 (double_nz  tN tb))).
have ns1: natp s1.
  apply: finite_sum_finite; split.
    hnf; aw; move => t ts; bw => //; case/setC1_P: ts => [ta tb]. 
    by move: (Hb _ ta tb) => [tc ->]; apply: (NS_Fib (NS_double tc)).
  aw; apply: sub_finite_set  (finite_set_nat (NS_succ hN)); apply: sub_setC.
have cs2: cardinalp s2 by rewrite /s2 /csumb; fprops.
rewrite - (Nsucc_rw ns1) (csum0r cs2).
rewrite /csumb; congr csucc; congr csum; apply: Lg_exten.
move => t/setC_P [ta /set1_P tb]; exact: (proj2 (Hb _ ta tb)).
Qed.
End FibP2.
    
(** ** EIII-5-8 Combinatorial analysis *)

Theorem shepherd_principle f c: function f -> 
  (forall x, inc x (target f) -> cardinal (Vfi1 f x) = c) ->
  cardinal (source f) = (cardinal (target f)) *c c.
Proof.  
move=> ff cc.
set (pa := Lg (target f) (Vfi1 f)).
have md: (mutually_disjoint pa). 
  apply: mutually_disjoint_prop.
  rewrite/pa  /Vfi1/Vfi; aw=> i j y it jt; rewrite !LgV// => sa sb.
  by rewrite  (iim_fun_set1_hi ff sa)  (iim_fun_set1_hi ff sb).
have <-: unionb pa = source f. 
  set_extens x. 
    rewrite /pa; move /setUb_P; aw; move => [y ytf]; rewrite LgV//. 
    move /iim_fun_P => [u /set1_P -> Jg];Wtac.
  move => xsf; move: (Vf_target ff xsf)=> Wt.
  apply /setUb_P; exists (Vf f x); rewrite /pa ? LgV //; aw; trivial.
  by apply: iim_fun_set1_i.
transitivity (csum pa). 
  apply :Eqc_disjointU; fprops.
  by rewrite /disjointU_fam; split;aww => i id; rewrite LgV //;aw. 
rewrite cprod2cl cprodC - csum_of_same (csum_pr pa) /pa; aw.
by apply: csumb_exten; rewrite /pa; aw => t tf; rewrite LgV//; apply: cc.
Qed.

Definition factorial n := cprodb n csucc.

Lemma CS_factorial n: cardinalp (factorial n).
Proof. by apply:CS_cardinal. Qed.

Lemma factorial_succ n: natp n ->
  factorial (csucc n) = (factorial n) *c (csucc n).
Proof. move=> nN; exact:(induction_on_prod csucc nN). Qed.

Lemma factorial0: factorial \0c = \1c.
Proof. by rewrite /factorial cprod_trivial0. Qed.

Lemma factorial1: factorial \1c = \1c.
Proof. 
by rewrite - succ_zero (factorial_succ NS0) factorial0 (cprod1l (CS_succ _)).
Qed.

Lemma factorial2: factorial \2c = \2c.
Proof.  
rewrite - succ_one.
rewrite (factorial_succ NS1) factorial1 succ_one cprod1l; fprops.
Qed.

Lemma factorial_nz n: natp n -> factorial n <> \0c.
Proof.
move: n;apply: Nat_induction.
  rewrite factorial0;  exact: card1_nz.
move=> m mN u; rewrite (factorial_succ mN).
apply: cprod2_nz =>//; apply: succ_nz.
Qed.

Lemma NS_factorial n: natp n -> natp (factorial n).
Proof.
move: n;apply: Nat_induction; first by rewrite factorial0; fprops.
move=> m mN u; rewrite (factorial_succ mN); fprops.
Qed.

Hint Resolve  factorial_nz: fprops.

Lemma factorial_prop f: f \0c = \1c ->
  (forall n, natp n -> f (csucc n) =  (f n) *c (csucc n)) ->
  forall x, natp x -> f x = factorial x.
Proof.
move=> fz fp; apply: Nat_induction; first by rewrite factorial0.
move=> m mN u; rewrite (factorial_succ mN) (fp _ mN) u // .
Qed.

Lemma factorial_induction n: natp n ->
 factorial n = induction_term  (fun a b => b  *c(csucc a)) \1c n.
Proof.
move: n;apply: Nat_induction.
  by rewrite factorial0 induction_term0.
by move=> m mN h; rewrite (factorial_succ mN) (induction_terms _ _ mN) h.
Qed.

Lemma quotient_of_factorials a b:
  natp a -> natp b -> b <=c a ->
  (factorial b) %|c (factorial a).
Proof. 
move=> aN bN ab; rewrite -(cdiff_rpr ab).
move: (NS_diff b aN).
set (c :=  a -c b);rewrite csumC; move: c; apply: Nat_induction.
  by rewrite (Nsum0r bN); apply: cdivides_itself; apply: NS_factorial.
move => n nN.
rewrite (csum_nS _ nN) (factorial_succ (NS_sum bN nN)).
apply: cdivides_trans2; fprops.
Qed.

Lemma quotient_of_factorials1 a b: 
  natp a -> natp b -> b <=c a ->
  (factorial (a -c b)) %|c (factorial a).
Proof. 
move=> aN bN leab; apply: (quotient_of_factorials aN);  fprops. 
exact:cdiff_ab_le_a (proj32 leab).
Qed.


Lemma factorial_monotone a b: natp b -> a <=c b ->
     factorial a <=c factorial b.
Proof.
move => bN leab. move:(NS_le_nat leab bN) => aN.
apply: (cdivides_smaller (quotient_of_factorials bN aN leab)).
apply: (factorial_nz bN).
Qed.

Definition falling_factorial a b := cprodb b (fun i => a -c i).
Notation "n ^_c m" := (falling_factorial n m)
  (at level 30, right associativity).

Lemma ffactn0 n : n ^_c \0c = \1c.
Proof. apply cprod_trivial0. Qed.

Lemma ffactnSr n m : natp m -> n ^_c (csucc m) = n ^_c m *c (n -c m).
Proof.
move =>  mN. apply: (induction_on_prod _ mN).
Qed.
  
Lemma ffactn1 n : natp n ->  n ^_c \1c = n.
Proof. 
move => nN.
rewrite  - succ_zero (ffactnSr _ NS0) ffactn0 (cdiff_n0 nN) cprod1l; fprops.
Qed.  

Lemma NS_ffact n m: natp n -> natp m -> natp (n ^_c m).
Proof.
move => nN; move: m; apply: Nat_induction.
  rewrite ffactn0; apply: NS1.
move => m mN Hr; rewrite (ffactnSr _ mN); apply: (NS_prod Hr); fprops.
Qed.


Lemma ffactnS n m :  natp n -> natp m ->
  n ^_c  (csucc m) = n *c (cpred n) ^_c m.
Proof.
move => nN mN.
move: m mN n nN; apply: Nat_induction.
  by move => n nN; rewrite ffactn0 succ_zero (ffactn1 nN) (cprod1r (CS_nat nN)).
move => m mN Hrec n nN.
rewrite (ffactnSr _ mN) (ffactnSr _ (NS_succ mN)).
rewrite (Hrec n nN) - cprodA.
case: (equal_or_not n \0c) => nz; first by rewrite nz !cprod0l.
by move: (cpred_pr nN nz) => [qa qb]; rewrite {3} qb cdiff_pr6.
Qed.
  

  
Lemma ffactSS n m : natp n -> natp m ->
  (csucc n) ^_c (csucc m) = (csucc n) *c n ^_c m. 
Proof.
by move => nN mN; rewrite (ffactnS (NS_succ nN) mN) cpred_pr2.
Qed.

Lemma ffact_small n m : natp m -> n <c m -> n ^_c m = \0c.
Proof.
move => mN.
move: m mN n; apply: Nat_induction; first by  move=> n /clt0.
move => m mN Hrec n lt.
move:(NS_lt_nat lt (NS_succ mN)) => nN.
rewrite (ffactnS nN mN).
case: (equal_or_not n \0c) => nz; first by rewrite nz cprod0l.
move: (cpred_pr nN nz) => [sa sb].
move: lt; rewrite {1} sb => /(cltSSP (CS_nat sa) (CS_nat mN)) /Hrec ->.
by apply: cprod0r.
Qed.


Lemma ffact_gt0 n m : natp n ->  m <=c n ->  n ^_c m <> \0c.
Proof.
move => nN le; move: (NS_le_nat le nN) => mN.
move: m mN n nN le; apply: Nat_induction.
   move => n _ _; rewrite ffactn0; fprops.
move => m mN Hrec n nN le.
case: (equal_or_not n \0c) => nz.
 by  move: le; rewrite nz => /cle0 /succ_nz.
move: (cpred_pr nN nz) => [sa sb].
rewrite (ffactnS nN mN); apply: cprod2_nz; first by  rewrite sb; apply:succ_nz.
by apply: (Hrec _ sa);apply/(cleSSP (CS_nat mN) (CS_nat sa)); rewrite - sb.
Qed.
 

Lemma ffactnn n : natp n ->  n ^_c n = factorial n.
Proof.
move: n; apply: Nat_induction; first by rewrite ffactn0 factorial0.
move => n nN Hrec; rewrite (ffactnS (NS_succ nN) nN) (cpred_pr2 nN) Hrec.
by rewrite cprodC factorial_succ.
Qed.

Lemma ffact_fact n m : natp n -> natp m ->
 m <=c n -> n ^_c m *c factorial (n -c m) = factorial n.
Proof.
move => nN; move: n nN m; apply: Nat_induction.
  by move => m mN /cle0 ->;  rewrite cdiff_0n ffactn0 factorial0 (cprod1r CS1).
move => n nN Hrec m mN.
have snN := (NS_succ nN).
case: (equal_or_not m \0c) => mz.
  by rewrite mz ffactn0 (cdiff_n0 snN) (cprod1l (CS_nat(NS_factorial snN))).
move:(cpred_pr mN mz) => [pN  ->].
move/(cleSSP (CS_nat pN) (CS_nat nN)) => lemn.
rewrite (cdiff_pr6 nN pN) (ffactnS snN pN) (cpred_pr2 nN) - cprodA.
by rewrite (Hrec _ pN lemn) cprodC factorial_succ.
Qed.

Lemma ffact_factd n m : natp n -> natp m -> m <=c n ->
  n ^_c m = (factorial n) %/c factorial (n -c m).
Proof.
move => nN mN le; move: (NS_diff m nN) => dN.
move: (NS_factorial dN) (NS_ffact nN mN) => qa qb.
by rewrite -(ffact_fact nN mN le) cprodC (cdivides_pr4 qa qb (factorial_nz dN)).
Qed.



Lemma card_injections E F:
  finite_set E -> finite_set F -> 
  cardinal (injections E F)  =  (cardinal F) ^_c (cardinal E).
Proof.
move=> fse fsF.
set (n:= cardinal F).
have nN: natp n by apply /NatP.
move: E fse (fse); apply: finite_set_induction0.
  rewrite cardinal_set0 ffactn0 => _.
  set f:= empty_function_tg F.
  suff ->: (injections emptyset F = singleton f) by rewrite cardinal_set1. 
  move: (empty_function_tg_function F) => [pa pb pc].
  have aux: inc f (functions emptyset F) by apply/functionsP.
  have injf: injection f by split => //; rewrite /f pb => x y; case; case.
  have ff: inc f (injections emptyset F) by apply/injectionsP.
  apply: set1_pr => // z /Zo_S vs; exact: (fun_set_small_source vs aux). 
move=> E a sE naE h.
move: (sub_finite_set (@sub_setU1 E a) h) => fse.
move/NatP: (fse);set (m := cardinal E) => mN.
rewrite  (csucc_pr naE) (ffactnSr _ mN) -(sE fse); clear sE h.
set (G2:= injections (E +s1 a) F). 
set (G1:= injections E F).
set rf:=Lf (restriction ^~  E) G2 G1.
have <-: (source rf = G2) by rewrite /rf; aw.  
have <-: (target rf = G1) by rewrite /rf; aw. 
have ta: lf_axiom (restriction  ^~ E) G2 G1. 
  move=> t /injectionsP [[ft it] st tt].
  have sat: sub E (source t) by rewrite st; fprops.
  move: (restriction_prop ft sat) => pp; move: (pp) => [pa pb pc].
  apply/injectionsP; split => //; [ split => // x y; rewrite pb => xE yE| ue].
  by rewrite restriction_V // restriction_V //; apply: it; apply:sat.
have fr: function rf by apply: lf_function.
apply: (shepherd_principle fr) =>  x.
set(K:= Vfi1 rf x).
rewrite lf_target; move/injectionsP => [injx sxE txF]; move: (proj1 injx) => fx.
have fst: finite_set (target x) by hnf;rewrite txF;fprops. 
move:(cardinal_complement_image injx fst).
set (C:= F -s (Imf x)).  
rewrite sxE txF -/n -/m -/C => <-.
have tav:(lf_axiom (Vf ^~ a) K C). 
  move => z /iim_fun_P [u /set1_P uz h1]; move: (Vf_pr fr h1).
  move: (p1graph_source fr h1); rewrite /rf lf_source => tG2.   
  rewrite LfV // => xx.
  move: tG2 =>  /injectionsP [[fz iz] sz tgz].
  have asz: inc a (source z) by rewrite sz; fprops.
  apply /setC_P; split; first by rewrite -tgz;Wtac.
  move /(Imf_P fx) => [y ysx].
  have Ez: sub E (source z) by rewrite sz; fprops.
  have yE: inc y E by ue.
  rewrite - uz xx (restriction_V fz Ez yE) => /(iz _ _ asz  (Ez _ yE)).
  by move => ya; case: naE; rewrite ya.
set (val:= Lf (Vf ^~ a) K C).
have fv: function val by apply: lf_function. 
have sv: (source val = K) by rewrite /val; aw.
have tv: (target val = C) by rewrite /val; aw.
apply /card_eqP; exists val; split => //; apply: lf_bijective =>//.
  move=> u v /iim_fun_P [u' /set1_P usx Jg1]. 
  move => /iim_fun_P [v' /set1_P vsx Jg2] sv1.
  have uG2:inc u G2 by move:(p1graph_source fr Jg1); rewrite /rf; aw.
  have vG2:inc v G2 by move:(p1graph_source fr Jg2); rewrite /rf; aw.
  move: (Vf_pr fr Jg1) (Vf_pr fr Jg2); rewrite /rf LfV //LfV //.
  move: uG2 => /injectionsP [[fu inju] su tu].
  move: vG2 => /injectionsP [[fvv injvØ]svv tvv] sr1 sr2.
  apply: function_exten=>//; [ue | ue | rewrite su].
  move=> t; case /setU1_P => tE; [ transitivity (Vf x t) | by rewrite tE].
    rewrite - usx  sr1 restriction_V //; rewrite su; fprops.
  rewrite - vsx sr2 restriction_V //; rewrite svv; fprops.
move=> y /setC_P [yF nyi].
have nasc: ~ (inc a (source x)) by ue.
set (f:= extension x a y).
have ff: function f by rewrite /f; apply: extension_f=>//. 
have sf: source f = E +s1 a by rewrite /f /extension; aw; ue.
have tf: target f = F by rewrite - (setU1_eq yF) - txF /f/extension; aw. 
have injf: injection f. 
  split =>//; move=> u v;rewrite sf /f;case /setU1_P => xsf; case /setU1_P=>ysf.
  - rewrite !extension_Vf_in //; try ue; apply: (proj2 injx); ue.
  - rewrite - sxE in xsf.
    rewrite ysf extension_Vf_out // extension_Vf_in //.
    move=> eq; rewrite -eq in  nyi; case: nyi.
    apply /(Imf_P fx); ex_tac; apply: W_pr3 =>//.
  - rewrite - sxE in ysf.
    rewrite xsf extension_Vf_out // extension_Vf_in //.
    move=> eq; rewrite eq in  nyi; case: nyi.
    apply /(Imf_P fx);ex_tac; apply: W_pr3 =>//.
  - by rewrite xsf ysf.
have rFE:(restriction f E = x).
  have se: sub E (source f) by rewrite sf; fprops.
  move: (restriction_prop ff se) => [pa pb pc].
  apply: function_exten=>//; rewrite ? pb //.  
    by rewrite pc tf txF.
    move=> u uE /=; rewrite restriction_V // /f extension_Vf_in//; ue.
have fG2: inc f G2 by apply/injectionsP. 
have fi:inc f (Vfi1 rf x).
  apply /iim_fun_P;exists x;fprops.
  have <-: (Vf rf f = x) by rewrite /rf LfV.  
  by apply: Vf_pr3=>//; rewrite /rf;aw.
by ex_tac; rewrite /f extension_Vf_out. 
Qed.

Lemma number_of_injections_spec E F:
  finite_set F -> E <=cc  F ->
  cardinal (injections E F)  = 
  factorial (cardinal F) %/c factorial  (cardinal F -c cardinal E).
Proof.
move => ha hb.
have nN: natp (cardinal F) by apply /NatP.
have mN: natp (cardinal E) by apply: (NS_le_nat hb nN).
have hc: finite_set E  by apply /NatP.
by rewrite (card_injections hc ha) (ffact_factd nN mN hb).
Qed.
  

Lemma permutation_Si E x:
   inc x (permutations E) -> inc (inverse_fun x) (permutations E).
Proof. by move/permutationsP => /inverse_bij_bp /permutationsP. Qed.

Lemma permutation_id E: inc (identity E) (permutations E).
Proof.
move:(identity_prop E) => [_ pa pb].
apply/permutationsP;split => //; apply: identity_fb.
Qed.

Lemma permutations_set0:
  (permutations emptyset) = singleton (identity emptyset).
Proof.
apply: set1_pr; first exact:(permutation_id emptyset).
move => a /permutationsP [[[fa _] _] sa ta].
by apply: function_exten; aww;  rewrite sa => t /in_set0.
Qed.  



Lemma permutation_Sc E x y:
   inc x (permutations E) -> inc y (permutations E) ->
   inc (x \co y) (permutations E).
Proof. 
move=> /permutationsP xp /permutationsP yp; apply /permutationsP. 
apply: (compose_bp yp xp).
Qed.

Lemma permutation_coP E x y:
   inc x (permutations E) -> inc y (permutations E) ->
   (x \coP y).
Proof. 
move=> /permutationsP [[[fy _] _] sx _] /permutationsP [[[h _] _] _ ty].
by split => //; rewrite ty.
Qed.

Lemma permutation_A E x y z:
  inc x (permutations E) -> inc y (permutations E) -> inc z (permutations E) ->
  x \co (y \co z) = (x \co y) \co z.
Proof. 
move=> ha hb hc;apply: (compfA (permutation_coP ha hb)(permutation_coP hb hc)).
Qed.

Lemma permutation_lK E x y:
  inc x (permutations E) -> inc y (permutations E) ->
  (inverse_fun x) \co (x \co y) = y.
Proof.
move => ha hb; apply:compf_lK (permutation_coP ha hb).
by move/permutationsP:ha => [].
Qed.

Lemma compf_lK' f g: 
  bijection g -> function f -> target g = target f -> 
   g \co (inverse_fun g \co f) = f.
Proof.
move => bg ff tf.
move:(inverse_bij_fb bg) => ibg.
move: (ifun_involutive (proj1 (proj1 bg))) => ffi.
rewrite -{1} ffi; apply: (compf_lK ibg); saw; fct_tac.
Qed.


Lemma compf_rK' f g: 
  bijection g -> function f -> source f = source g -> 
  (f \co inverse_fun g) \co g = f.
Proof.
move => bg ff tf.
move:(inverse_bij_fb bg) => ibg.
move: (ifun_involutive (proj1 (proj1 bg))) => ffi.
rewrite -{2} ffi; apply: (compf_rK ibg); saw; fct_tac.
Qed.



Lemma permutation_lK' E x y:
  inc x (permutations E) -> inc y (permutations E) ->
  x \co ( (inverse_fun x) \co y) = y.
Proof.
move => ha hb. 
move/permutationsP:(ha) => [[[/ifun_involutive hc _] _] _ _].
rewrite -{1} hc;apply:(permutation_lK (permutation_Si ha) hb).
Qed.

Lemma permutation_rK E x y:
  inc x (permutations E) -> inc y (permutations E) ->
  (x \co y) \co (inverse_fun y) = x.
Proof.
move => ha hb; apply:compf_rK (permutation_coP ha hb).
by move/permutationsP:hb => [].
Qed.

Lemma permutation_if_inj E f: finite_set E -> function_prop f E E -> 
  injection f -> inc f (permutations E).
Proof.
move => fse [ff sf tf] ijf; apply/permutationsP; split=> //.
by apply: bijective_if_same_finite_c_inj => //; rewrite sf // tf.
Qed.

Lemma permutations_finite E: finite_set E ->
   permutations E = injections E E.
Proof.
move => h; set_extens t => /Zo_P [ha hb].
  by move:(proj1 hb) => injf;  apply:Zo_i.
by apply:(permutation_if_inj h) hb; apply /functionsP.
Qed.

Lemma card_permutations E:  finite_set E ->
  cardinal (permutations E)  = (factorial (cardinal E)).
Proof. 
move=> fsE.
have cE: natp (cardinal E) by fprops.
rewrite (permutations_finite fsE).
by rewrite (card_injections fsE fsE) (ffactnn cE).
Qed.

Lemma perm_int_inj n f: natp n -> inc f (permutations n) ->
    (forall x y, x <c n -> y <c n -> Vf f x = Vf f y -> x = y).
Proof.
move => nN /permutationsP[ [[_ H] _] sf _].
rewrite sf in H.
by move => x y /(NltP nN) xs /(NltP nN) ys sv; apply:H.
Qed.

Lemma perm_int_surj n f: natp n -> inc f (permutations n) ->
   forall y, y <c n -> exists2 x, x <c n & Vf f x = y.
Proof.
move => nN /permutationsP[ [_ [_ H]] sf tf].
rewrite sf tf in H.
by move => y /(NltP nN) /H [x /(NltP nN) sa sb]; exists x.
Qed.

Lemma transposition_prop n i j 
   (f:=Lf (fun z => variant i j (variant j i z z) z) n n):
   natp n -> inc i  n -> inc j n ->
   [/\ inc f (permutations n), Vf f i = j, Vf f j = i,
     forall k, inc k n -> k <> i -> k <> j -> (Vf f k)  = k &
     forall k, inc k n -> Vf f (Vf f k) = k].
Proof.
move => nN iE jE.
have ax: lf_axiom (fun z => variant i j (variant j i z z) z) n n.
  rewrite /variant => z; Ytac h1; [ ue | Ytac h2; [ ue | done]].
have pa: Vf f i = j by rewrite /f LfV // variant_true0.
have pb: Vf f j = i by rewrite /f/variant LfV//; Ytac h1 => //; Ytac0.
have pc: forall k, inc k n -> k <> i -> k <> j -> Vf f k = k.
  by move => k kE ki kj; rewrite /f LfV// !variant_false.
have pd:forall k, inc k n -> Vf f (Vf f k) = k.
  move => k kE; case (equal_or_not k i) => ki; first by rewrite ki pa pb.
  case (equal_or_not k j) => kj; first by rewrite kj pb pa.
  by rewrite !(pc _ kE ki kj).
have sf: source f =  n by rewrite /f;aw.
have tf: target f =  n by rewrite /f;aw.
have ff: function f by  apply: (lf_function ax).
have bf: bijection f.
  split; split => //; first by rewrite sf => u v  /pd {2} <- /pd {2} <- ->.
  rewrite sf tf => y ye;exists (Vf f y); [ Wtac | by rewrite pd].
by split => //; apply /permutationsP. 
Qed.

Lemma extension_perm n s (es := extension s n n):
  natp n -> inc s (permutations n) ->
  [/\ inc es (permutations (csucc n)), Vf es n = n &
    forall i, inc i n -> Vf es i = Vf s i]. 
Proof.
move => nN /permutationsP [bs ss ts].
have Ha: ~ inc n (source s) by rewrite ss; apply:(Nat_decent nN).
have Hb: ~ inc n (target s) by rewrite ts -{2} ss.
split.
- apply/permutationsP; split.
  + exact:(extension_fb Ha Hb bs).
  + by rewrite /es /extension; aw; rewrite ss (succ_of_nat nN).
  + by rewrite /es /extension; aw; rewrite ts (succ_of_nat nN). 
- by rewrite (extension_Vf_out n (proj1 (proj1 bs)) Ha).
- rewrite - ss;move => i lin.
  by rewrite (extension_Vf_in n (proj1 (proj1 bs)) Ha). 
Qed.
        
Lemma rotation_prop n (m := csucc n)
      (f := Lf (fun i => variant \0c n (cpred i) i) m m)
   (g := Lf (fun i => variant n \0c (csucc i) i) m m):
  natp n -> 
  [/\ inc f (permutations m), inc g (permutations m),  inverse_fun f = g &
     [/\ Vf f \0c = n, forall i, i <c n -> Vf f (csucc i) = i,
         forall i, i <=c n -> i <> \0c -> Vf f i = (cpred i), 
      Vf g n = \0c &  forall i, i <c n -> Vf g i = (csucc i)  ] ].
Proof.
move => nN.
move: (NleP nN) => H.
have axf: lf_axiom (fun i => variant \0c n (cpred i) i) m m.
  rewrite /variant => i /H lin; apply/H. 
  Ytac h; first by  apply: (cleR (CS_nat nN)).
  exact: (cleT (cpred_le (proj31 lin)) lin).
have axg: lf_axiom (fun i => variant n \0c (csucc i) i)  m m.
  move => i /H lin; apply/H; rewrite /variant; Ytac h; first by  apply:cle0n.
  by apply/(cleSltP (NS_le_nat lin nN)). 
have i0m: inc \0c m by apply/H; apply:cle0n.
have rA: Vf f \0c = n by rewrite /f/variant LfV//; Ytac0.
have rB: forall i, i <c n -> Vf f (csucc i) = i.
  move => i lin.
  have sin: inc (csucc i) m by apply/H; apply/(cleSltP (NS_lt_nat lin nN)).
  rewrite/f LfV//.
  by rewrite (variant_false _ _ (@succ_nz _)) (cpred_pr1 (proj31_1 lin)).
have rC: forall i, i <=c n -> i <> \0c -> Vf f i = (cpred i). 
  move => i lin inz.
  move: (cpred_pr (NS_le_nat lin nN) inz) =>[pN pv].
  rewrite {1} pv rB //; apply/(cleSltP pN); ue.
have rD: Vf g n = \0c.
 rewrite/g LfV//? variant_true //; apply/H; apply: (cleR (CS_nat nN)).
have rE: forall i, i <c n -> Vf g i = csucc i.
  by move => i [lin nn]; rewrite/g LfV// ? variant_false//; apply/H.
have fg_val i: inc i m -> Vf f (Vf g i) = i.
  move => /H lin; case: (equal_or_not i n) => inn.
     by rewrite inn rD rA.   
  by move:(conj lin inn)=> Hi;  rewrite (rE _ Hi) (rB _ Hi).  
have gf_val i: inc i m -> Vf g (Vf f i) = i.
  move => /H lin; case: (equal_or_not i \0c) => iz.    
    by rewrite iz rA rD. 
  move: (cpred_pr (NS_le_nat lin nN) iz)  =>[pN pv].
  rewrite (rC _ lin iz) rE- ? pv //; apply/(cleSltP pN); ue.
have [ff sf tf]: function_prop f m m.
  by rewrite/f;saw; apply:lf_function.
have [fg sg tg]: function_prop g m m.
  by rewrite/g;saw; apply:lf_function.
have cgfp: g \coP f by split => //; ue.
have cfgp: f \coP g by split => //; ue.
have cgf: g \co f = identity (source f).
   apply: identity_prop0; first by saw; [  apply:compf_f| ue ].
   move => i isf; rewrite compfV// gf_val  //; ue.
have cfg: f \co g = identity (source g).
   apply: identity_prop0; first by saw; [  apply:compf_f| ue ].
   move => i isf;rewrite compfV// fg_val  //; ue.
move:(bijective_from_compose  cgfp cfgp cgf cfg) => [bf bg fgi].
split.
-  by apply/permutationsP.
-  by apply/permutationsP.
- done.
- done.
Qed.

Lemma permutation_exists1 n i: natp n -> i <c n ->
    exists2 f, inc f (permutations n) & Vf f \0c = i.
Proof.
move => nN lin.
move /(NltP nN): (cle_ltT (cle0x (proj31_1 lin)) lin) => oE.
move /(NltP nN):lin => iI.
move:(transposition_prop nN iI oE) => [pa _ pb _ _];ex_tac.
Qed.

Lemma partial_rotation n f (k := Vf (inverse_fun f) n)
      (g:= fun i => Yo (i <c k) (Vf f i) (Vf f (csucc i)))
      (G := Lf g n n):
  natp n -> inc f (permutations (csucc n)) ->
  [/\ k <=c n, Vf f k = n, lf_axiom g n n & inc G (permutations n)].   
Proof.
move => nN /permutationsP H.
move: (inverse_bij_bp H) => hh.
have nsf: inc n (csucc n) by apply:Nsucc_i.
move: H => [bf sf tf].
have IP := (NltP nN).
have IP' := (NltP (NS_succ nN)).
have ff: function f by fct_tac.
have iff:= (proj2 (proj1 bf)).
have ntf: inc n (target f) by rewrite tf. 
move: (inverse_V bf ntf); rewrite -/k => kv.
have lekn: k <=c n.
  move: hh => [[[bg _] _] sg tg]; apply/(NleP nN); rewrite/k; Wtac.
have kN:=(NS_le_nat lekn nN).
have ksf: inc k (source f) by rewrite sf; apply/IP'; apply/cltSleP.
have Gv i: g i =  Vf f (Yo (i <c k) i (csucc i)) by rewrite/g; Ytac h; Ytac0.
have Gs i: i <c n -> inc  (Yo (i <c k) i (csucc i)) (source f).
  move => lin; rewrite sf; apply /IP'.
  by Ytac h; [ apply:(clt_ltT lin (cltS nN)) | apply :cltSS].
have axg:  lf_axiom g n n.
  move => i /IP lin;move: (Gs _ lin) => usf;rewrite Gv; apply /IP.
  split; first by apply/(cltSleP nN); apply/IP'; Wtac.
  rewrite - kv => /(iff _ _ usf ksf).
  Ytac h => eq; first by case (proj2 h).
  by case: h; rewrite - eq; apply:(cltS (NS_lt_nat lin nN)).
split => //.
apply/permutationsP; rewrite/G;split; aw; trivial.
apply: lf_bijective => //.
  move => u v /IP ui /IP vi.
  rewrite Gv Gv; move/(iff _ _ (Gs _ ui) (Gs _ vi)); Ytac h1; Ytac h2 => eq. 
  - exact.
  - case: h2; apply:cle_ltT h1; rewrite eq; exact: (cleS (NS_lt_nat vi nN)). 
  - case: h1; apply:cle_ltT h2; rewrite - eq; exact: (cleS (NS_lt_nat ui nN)). 
  - by apply: (csucc_inj (proj31_1 ui) (proj31_1 vi)).
move => y /IP yi; move:(clt_ltT yi (cltS nN)) => yi'.
have ytf: inc y (target f) by rewrite tf; apply/IP'.
move: (proj2 (proj2 bf) _ ytf) => [x xsf ea]; rewrite ea.
move: xsf; rewrite sf => /IP' xsn.
have xN:= (NS_lt_nat xsn (NS_succ nN)).
case: (NleT_ell kN xN) => cix.
+ by move:(f_equal (Vf f) cix); rewrite kv -ea; move => eb; case: (proj2 yi).
+ case (equal_or_not x \0c) => xnz. 
    rewrite xnz in cix;case:(clt0 cix).
  move: (cpred_pr xN xnz) => [sc sd].
  move: xsn; rewrite sd;move/(cltSSP (CS_nat sc) (CS_nat nN)) => /IP ci.
  exists (cpred x) => //; rewrite - sd /g; Ytac h; last by rewrite - sd.
 by move/(cleSlt0P (CS_nat sc) kN):h; rewrite - sd => /(cltNge cix).
exists x; [ apply /IP; exact:(clt_leT cix lekn) | by rewrite /g; Ytac0].
Qed.

(** Enumerating a finite set of integers *)

Lemma finite_total_enum r (f := (the_ordinal_iso r))
      (n := cardinal (substrate r)):
  total_order r -> finite_set (substrate r)  ->
  [/\ natp n, bijection_prop f  n (substrate r),
       forall i j, i <c n -> j <c n -> (i <=c j <-> gle r (Vf f i) (Vf f j)),
       forall i j, i <c j -> j <c n -> glt r (Vf f i) (Vf f j) &
       forall i, natp i -> csucc i <c n -> glt r (Vf f i) (Vf f (csucc i))].
Proof.
move => ha hb.
move: (finite_set_torder_wor ha hb) => wor.
move:(the_ordinal_iso1 wor); rewrite -/f; move =>[on pr fp fsi].
have nN: natp n by  apply/card_finite_setP.
move: fp; rewrite ordinal_o_sr => fp.
have eq1: cardinal (ordinal r) = n by  move/card_eqP : (equipotent_bp fp).
have fsp: finite_set (ordinal r) by  apply/card_finite_setP; rewrite eq1.
move: (card_card (CS_finite_o (ordinal_finite1 (OS_ordinal wor) fsp))).
rewrite eq1 => rb.
rewrite - rb in fp.
move:(fp) =>[[[_ qa] _] sf tf].
have rc i j:  i <c n -> j <c n -> (i <=c j <-> gle r (Vf f i) (Vf f j)).
  move => lin ljn; move:(proj31_1 lin) (proj31_1 ljn) => co cij.
  move/(NltP nN):lin =>  lin; move /(NltP nN): ljn => ljn.
  move: (fsi i j); rewrite sf => fs.
  move:(fs lin ljn) (ordo_leP (ordinal r) i j); rewrite - rb => Ha Hb.
  split; first by move => /proj33 h; apply/ Ha/Hb.
  by move=> /Ha/Hb /proj33 h.
have rd i j: i <c j -> j <c n -> glt r (Vf f i) (Vf f j).
  move => [lij nij] ljn; move: (cle_ltT  lij ljn) => lion.
  have isf: inc i (source f) by rewrite sf; apply/NltP.
  have jsf: inc j (source f) by rewrite sf; apply/NltP.
  by split; [ apply/rc |  move/(qa _ _ isf jsf)].
by split => // i iN lsi; apply: rd => //; apply: cltS.
Qed.



Definition nth_more K S := S +s1 intersection (K -s S).
Definition nth_elts K := induction_term (fun _ S => nth_more K S) emptyset.

Lemma nth_set0 x (y := intersection x) : x = emptyset -> y = \0c.
Proof. by rewrite /y;move => ->; rewrite setI_0. Qed.

Lemma nth_set2 K S: sub K S ->  nth_more K S = S +s1 \0c. 
Proof. by move => h; rewrite  /nth_more (setC_T h) setI_0. Qed.

Lemma nth_set3 K: nth_more K K = K +s1 \0c. 
Proof. by apply:nth_set2. Qed.

Definition segment_nat K S := 
  sub S K /\  (forall i j, inc i S -> inc j (K -s S) -> i <c j).

Lemma nth_set4 K S (S':= nth_more K S) (x:= intersection (K -s S)):
   sub K Nat -> segment_nat K S -> S <> K ->
   [/\ segment_nat K S', inc x (S' -s S) & cardinal S' = csucc (cardinal S)].
Proof.
move => KN [sa sb sc].
have sd:=(setC_ne (conj sa sc)). 
have se:=(sub_trans (@sub_setC K S) KN).
move:(inf_Nat se sd); rewrite -/x; move => [/setC_P [xK xS] xm].
split; first split.
+ by move => t /setU1_P; case; [move /sa | move => ->].
+ move => i j /setU1_P iv /setC_P [jK /setU1_P jv].
  have [js /nesym ji]: ~(inc j S) /\ j <> intersection (K -s S).
    by split;dneg h; fprops.
  have aux: inc j (K -s S) by apply/setC_P. 
  case iv; first by move => iS; apply: sb => //. 
  by move ->; split => //; apply: xm. 
+ by apply/setC_P; split; [ apply:setU1_1 | ].
+ by rewrite csucc_pr.
Qed.

Lemma nth_elts0 K: nth_elts K \0c = emptyset.
Proof. by apply:induction_term0. Qed.

Lemma nth_elts_succ K n: 
  natp n -> nth_elts K (csucc n) = nth_more K (nth_elts K n).
Proof. apply:induction_terms. Qed.

Lemma nth_set5 K n (S:= nth_elts K n):  
   natp n -> sub K Nat -> n <=c cardinal K ->
   (segment_nat K S /\ cardinal S = n).
Proof.
rewrite /S => nN kN;move: n {S} nN; apply: Nat_induction.
  by rewrite nth_elts0 cardinal_set0; split=> //; split=> [ i | i j ] /in_set0.
move => n nN Hrec snk.
rewrite /nth_elts (induction_terms _ _ nN)  -/(nth_elts K n).
move:(Hrec (cleT (cleS nN) snk))  => [sa sb].
case (equal_or_not (nth_elts K n) K) => nsK.
  by move: (proj2 (clt_leT (cltS nN) snk)); rewrite - nsK sb.
by move: (nth_set4 kN sa nsK); rewrite sb; move => [ua _ ub].
Qed.


Lemma nth_set6 K (n:= cardinal K):
   natp n -> sub K Nat -> (nth_elts K n) = K.
Proof.
move => nN kN.
move: (nth_set5 nN kN (cleR (CS_nat nN))) => [[sa _] sb].
have fsk: finite_set K by apply /NatP.
exact: (cardinal_setC5 fsk sa sb). 
Qed.


Lemma nth_set_M K n m:
  natp n -> m <=c n -> sub (nth_elts K m) (nth_elts K n).
Proof.
move => nN mn.
rewrite - (cdiff_pr mn).
move:(NS_diff m nN); set k:= (n -c m) => kN.
move:(NS_le_nat mn nN) => mN; move: k kN;clear n mn nN.
apply: Nat_induction; first by rewrite (csum0r (CS_nat mN)).
move => n nN hrec.
rewrite (csum_nS _ nN) (nth_elts_succ _ (NS_sum mN nN)).
apply /(sub_trans hrec) /subsetU2l. 
Qed.
 
Definition nth_elt K n := union (nth_elts K (csucc n) -s nth_elts K n).

Lemma nth_set7 K n (S:= (nth_elts K n)) (x:= nth_elt K n) :
   natp n -> sub K Nat -> n <c cardinal K ->
   [/\ inc x (K -s S), inc x (nth_elts K (csucc n)),
       forall y, inc y (K -s S) -> x <=c y
     & forall y, inc y S -> y <c x].
Proof.
move => nN KN h1.
have [[SK sw] cs1]:= (nth_set5 nN KN (proj1 h1)).
have pa: sub  (K -s S) Nat by move => t/setC_P [/ KN h _].
case: (emptyset_dichot (K -s S)) => nek.
  by case: (proj2 h1); rewrite - cs1 {2} (extensionality (empty_setC nek) SK).
have h2: csucc n <=c cardinal K by apply /(cleSltP nN). 
move: (inf_Nat pa nek).
set I := intersection (K -s S); move => [sa sb].
have /setCId_Pl di: disjoint (singleton I) S.
  by apply: disjoint_pr => u /set1_P -> eis; case/setC_P: sa => _.
move: (erefl x); rewrite {1} /x /nth_elt /nth_elts (induction_terms _ _ nN).  
rewrite -/(nth_elts K n) /nth_more -/S -/I setCU2_l setC_v set0_U2 di setU_1.
by move => <-; split; fprops; move => y ys; apply: sw. 
Qed.

Lemma nth_elt_inK K n:  natp n -> sub K Nat -> n <c cardinal K ->
   inc (nth_elt K n) K. 
Proof. by move => pa pb pc; move:(nth_set7 pa pb pc) => [/setC_P []]. Qed.

Lemma nth_elt_ax K: sub K Nat -> natp (cardinal K) ->
   lf_axiom (nth_elt K) (cardinal K) K.
Proof.
move => KN kN n /(NltP kN) nk.
apply: (nth_elt_inK (NS_lt_nat nk kN) KN nk).
Qed.

Lemma nth_elt_monotone K n m:
   natp n -> sub K Nat -> n <c cardinal K ->
   m <c n -> (nth_elt K m) <c (nth_elt K n).
Proof.
move => nN KN nk mn.
have mN:= (NS_lt_nat mn nN).
apply: (proj44  (nth_set7 nN KN nk)). 
have ub:= (proj42 (nth_set7 mN KN (clt_ltT mn nk))).
move /(cleSltP mN): mn => le1.
exact:(nth_set_M nN le1 ub).
Qed.

Lemma nth_elt_bf K (f := Lf (nth_elt K) (cardinal K) K):
  sub K Nat -> natp (cardinal K) ->
  (bijection f /\ 
  forall i j,  inc i (source f) -> inc j (source f) -> i <c j ->
       Vf f i <c Vf f j). 
Proof.
move => KN  kN.
move: (nth_elt_ax KN kN) => ax.
have sf: source f = (cardinal K) by rewrite /f;aw.
have pa: forall i j,  inc i (source f) -> inc j (source f) -> i <c j ->
       Vf f i <c Vf f j. 
  rewrite /f;aw;move => i j isf jsf; rewrite !LfV //.
  move/(NltP kN): jsf => jk. 
  by apply:nth_elt_monotone => //; apply:(NS_lt_nat jk kN).
split; last by exact.
rewrite sf in pa.
move: (finite_set_nat kN) => fsk.
rewrite /f;apply: bijective_if_same_finite_c_inj; aw; trivial.
split; first by apply:lf_function.
rewrite sf => i j iK jK sv.
case: (NleT_ell (NS_inc_nat kN iK) (NS_inc_nat kN jK)) => cp //.
  by case: (proj2 (pa _ _ iK jK cp)). 
  by case: (proj2 (pa _ _ jK iK cp)). 
Qed.

Lemma nth_elt_surj K a: sub K Nat -> natp (cardinal K) -> inc a K ->
  exists2 n, n <c (cardinal K) & a = (nth_elt K n).
Proof.
move => ha hb aK; move:(nth_elt_bf ha hb) => [[_ [ff fs]] _].
have ax:= (nth_elt_ax ha hb).
move:fs; aw => fs; move:(fs _ aK) => [x xa]; rewrite LfV// => ->.
by exists x => //; apply/(NltP hb).
Qed.

Lemma nth_elt_exten k f: natp k -> 
   (forall i, i <c k  -> natp (f i)) ->
   (forall i j, i <c j -> j <c k  -> f i <c f j) ->
   (forall i, i<c k -> (nth_elt (fun_image k f) i = f i)).
Proof.
move => kN ha hb.
set K := (fun_image k f).
have Ka: sub K Nat by move => z /funI_P [i /(NltP kN) lik ->]; apply: ha.
move:(Nintco_wor k) => [wor1 sr1]; move: (proj1 wor1) => or1.
have csK: cardinal_set K by move => t /Ka /CS_nat.
move:(wordering_cle_pr csK) => [[]].
set r2 := graph_on cardinal_le K => or2 _ sr2.
have hc:lf_axiom f k K by move => t tk; apply/funI_P; ex_tac.
have hd:function_prop (Lf f k K) k K.
  by saw; apply:lf_function.
have he x y: inc y k -> (gle (Nint_co k) x y <->  x <=c y).
  move =>  /(NltP kN) yk; apply: (iff_trans(Nintco_gleP kN x y)).
  by split; first case.
have hf x y: inc x K -> inc y K -> (x <=c y <->  gle r2 x y).
  move => xK yK; split => h; first by apply/graph_on_P1.
  by move/graph_on_P1: h => [].
have finj:{inc k &, injective f}.
  move => i j /(NltP kN) lik /(NltP kN) ljk sf.
  case:(cleT_ell (proj31_1 lik) (proj31_1 ljk)) => // lij.
  - by case: (proj2 (hb _ _ lij ljk)); rewrite sf.
  - by case: (proj2 (hb _ _ lij lik)); rewrite sf.
have hg: bijection_prop (Lf f k K) k K.
  by saw;apply:lf_bijective => // y /funI_P.
have sf1: order_isomorphism (Lf f k K) (Nint_co k) r2.
  split => //; first by rewrite sr1 sr2 (NintE kN).
  hnf; aw => x y xK yK; rewrite !LfV//;apply:(iff_trans (he x y yK)).
  move: (hc _ xK) (hc _ yK) => fxk fyk.
  move/(NltP kN):(yK) => lyk;move/(NltP kN):(xK) => lxk.
  apply: (iff_trans _ (hf _ _ fxk fyk)).
  case:(cleT_ell (proj31_1 lxk) (proj31_1 lyk)) => lxy.
  - rewrite lxy; split => _; apply:cleR; first exact: (CS_nat (Ka _ fyk)).
    exact (proj31_1 lyk).
  - split => h; [ exact (proj1 (hb _ _ lxy lyk)) | exact:(proj1 lxy) ].
  - by split => h; [ move:(cltNge lxy h) | case:(cltNge (hb _ _ lxy lxk) h)].
have Kb: cardinal K = k.
  by rewrite - (card_nat kN); apply:cardinal_fun_image. 
have aux: natp (cardinal K) by rewrite Kb.
move:(nth_elt_ax Ka aux); rewrite Kb => hc'.
have hd':function_prop (Lf (nth_elt K) k K) k K.
  by saw; apply:lf_function.
have hg' : bijection_prop (Lf (nth_elt K) k K) k K.
  by saw; move:(proj1 (nth_elt_bf Ka aux)); rewrite Kb.
have sf2: order_isomorphism (Lf (nth_elt K) k K) (Nint_co k) r2.
  split => //; first by rewrite sr1 sr2 (NintE kN).
  hnf; aw => x y xK yK; rewrite !LfV//;apply:(iff_trans (he x y yK)).
  move: (hc' _ xK) (hc' _ yK) => fxk fyk. 
  move/(NltP kN):(yK) => lyk;move/(NltP kN):(xK) => lxk.
  apply: (iff_trans _ (hf _ _ fxk fyk)).
  case:(cleT_ell (proj31_1 lxk) (proj31_1 lyk)) => lxy.
  - rewrite lxy; split => _; apply:cleR; first exact: (CS_nat (Ka _ fyk)).
    exact (proj31_1 lyk).
  - split => h; last by exact:(proj1 lxy).
    have yb: y <c cardinal K by ue.
    exact: (proj1(nth_elt_monotone (NS_lt_nat lyk kN) Ka yb lxy)).
  - split => h; first by move:(cltNge lxy h).
    have xb: x <c cardinal K by ue.
    case:(cltNge (nth_elt_monotone (NS_lt_nat lxk kN) Ka xb lxy) h).
move => i /(NltP kN) ik. 
move: (f_equal (Vf^~i) (iso_unique wor1  sf2 sf1)); rewrite !LfV//.
Qed.

(* noter *)
Lemma sub_nat_finite K n: natp n -> sub K n -> natp (cardinal K).
Proof.
move => nN /sub_smaller; rewrite (card_nat nN) => h; apply:(NS_le_nat h nN).
Qed.


Lemma nth_elt_prop7 K n s: natp n -> inc K (\Po n) ->
   inc s (permutations (cardinal K)) -> nonempty K ->
   inc (nth_elt K (Vf s \0c)) K.
Proof.
move => nN /setP_P Kn /permutationsP [[[fs _] _] ss ts] ke.
have sKN: sub K Nat by move => t /Kn/(NltP nN) => h;apply(NS_lt_nat h nN).
move:(sub_smaller Kn); rewrite (card_nat nN) => ckn.
have ckN:=(NS_le_nat ckn nN).
have cknz:= (card_nonempty1 ke).
have zi: inc \0c (cardinal K).
  apply /(NltP ckN); split; [ apply: (cle0n ckN) | fprops].
have l1: (Vf s \0c) <c cardinal K by apply/(NltP ckN); Wtac; rewrite ss.
by move:(nth_set7 (NS_lt_nat l1 ckN) sKN l1) => [/setC_P []].
Qed.


Lemma nth_elt_prop8 K n a: natp n -> inc K (\Po n) -> inc a K ->
  exists2 f, inc f (permutations (cardinal K)) & a = nth_elt K (Vf f \0c).
Proof.
move => nN Ks1 aK.
have neK: nonempty K by ex_tac.
move/setP_P: (Ks1) => ka.
have sKN:= (sub_trans ka (NS_inc_nat nN)).
move:(sub_smaller ka); rewrite (card_nat nN) => ckn.
have cknz:= (card_nonempty1 neK).
have ckN:=(NS_le_nat ckn nN).
move:(cpred_pr ckN cknz); set k:= cpred _; move => [kN kv].
have fsk: finite_set K by apply/NatP.
move:(nth_elt_surj sKN ckN  aK) => [i il1 ->].
move: (permutation_exists1 ckN il1) => [f fp <-]; ex_tac.
Qed.


Definition nth_elt_dbl K n :=
  fun i => Yo (i <c (cardinal K)) (nth_elt K i)
              (nth_elt (n -s K) (i -c (cardinal K))).

Lemma nth_elt_dbl_prop K n: natp n -> inc K (\Po n) ->
  lf_axiom (nth_elt_dbl K n) n n
  /\ inc (Lf (nth_elt_dbl K n) n n) (permutations n).
Proof.
move => nN /setP_P sKn.
have snn: sub n Nat by  move => t /(NS_inc_nat nN).
have sKN:= sub_trans sKn snn.
move: (sub_nat_finite nN sKn) => kN.
move: (@sub_setC n K)=> pa.
move:(cardinal_setC2 sKn). rewrite (card_nat nN) - csum2cr - csum2cl => w.
have ax: lf_axiom (nth_elt_dbl K n) n n.
  rewrite /nth_elt_dbl.
  move => i /(NltP nN) lin; move: (NS_lt_nat lin nN) => iN.
  case: (NleT_el kN iN) => ha; [ rewrite (Y_false (cleNgt ha)) | Ytac0].
    move:(NS_diff  (cardinal K) iN) => diN.
    apply: (pa).
    apply:(nth_elt_inK diN (sub_trans pa snn)).
    by apply:(csum_lt2l kN diN (sub_nat_finite nN pa));rewrite (cdiff_pr ha)-w. 
  apply: sKn;apply:(nth_elt_inK iN sKN ha).
split => //; apply/permutationsP; saw.
apply:bijective_if_same_finite_c_surj; aw; trivial.
  by apply: finite_set_nat.
apply: (lf_surjective ax) => y yn.
case: (inc_or_not y K) => yK.
   move:(nth_elt_surj sKN kN yK) => [i lik ->]; exists i.
     move: (sub_smaller sKn); rewrite (card_nat nN) => le1.
     apply/(NltP nN); apply: (clt_leT lik le1).
   by rewrite /nth_elt_dbl; Ytac0.
have yK': inc y (n -s K) by apply/setC_P.
have sKN':= sub_trans pa snn.
move:(nth_elt_surj sKN'  (sub_nat_finite nN pa) yK')=> [i lik ->].
exists (i +c (cardinal K)).
  by apply/(NltP nN); rewrite w csumC; apply/csum_Meqlt.
rewrite /nth_elt_dbl Y_false.  by rewrite (cdiff_pr1' (proj31_1 lik) kN).
by apply/cleNgt; apply:(Nsum_Mle0 _ kN).
Qed.
  
Lemma nth_elt_dbl_prop1 n K (k := cardinal K)
  (s:= (Lf (nth_elt_dbl (K +s1 n) (csucc n)) (csucc n) (csucc  n))): 
 natp n -> inc K (\Po n) -> 
     [/\ inc s (permutations (csucc n)),
      k <=c n, K = fun_image k (Vf s), 
    Vf s k = n &
    (forall i j, i<c j -> j <c k -> (Vf s i) <c (Vf s j))].
Proof.
move => nN KP.
move: (NS_succ nN) => sN.
move/setP_P:KP => sKn.
have KF1: sub  (K +s1 n) (csucc n).
  move:(cleS nN) => /ocle /proj33 snn t /setU1_P []; first  by move /sKn /snn.
  by move => ->; apply/Nsucc_i.
move/setP_P: (KF1) => KF. 
have SKN: sub (K +s1 n) Nat by move => t /KF1 / (NS_inc_nat sN).
move: (nth_elt_dbl_prop sN KF); rewrite  -/s; move => [ax sp].
have nK: ~inc n K by  move/sKn; apply:Nat_decent.
move: (csucc_pr nK); rewrite  -/k => cK'.
move:(sub_smaller sKn); rewrite (card_nat nN) -/k => lekn.
have kN:= (NS_le_nat lekn nN).
have k1N: natp (cardinal (K +s1 n)) by rewrite cK'; apply: (NS_succ kN).
have kl1 := cltS kN.
have ha i: i <c (csucc k) ->  Vf s i = nth_elt (K +s1 n) i.
   move => lik; rewrite /s LfV//; first by rewrite /nth_elt_dbl cK'; Ytac0.
   by apply/(NltP sN); apply/(clt_leT lik); apply: cleSS.
have hb: forall x, inc x (K+s1 n) -> exists2 i, i <c (csucc k) & x = Vf s i.
  move => x xK; move: (nth_elt_surj SKN k1N xK); rewrite cK'.
  by move => [i lik ->]; rewrite -(ha _ lik); exists i.
have hc: forall i j, i <c j -> j <c (csucc k) -> Vf s i <c Vf s j.
  move => i j lij ljk; rewrite (ha _ ljk) (ha _ (clt_ltT lij ljk)).
  apply:(nth_elt_monotone (NS_lt_nat ljk (NS_succ kN)) SKN _ lij); ue.
have hd: forall i, i <c (csucc k) -> inc (Vf s i) (K +s1 n).
  move => i lik; rewrite (ha _ lik).
  apply:(nth_elt_inK (NS_lt_nat lik (NS_succ kN)) SKN); ue.
have sk: Vf s k = n.
  move:(hb _ (setU1_1 K n)) =>[ i lin nv].
  move: lin=> /(cltSleP kN) / cle_eqVlt; case; [ by move <- |  move => lik].
  move: (hc _ _ lik kl1); rewrite - nv; move => [np1 np2].
  move: (hd _ kl1) => /setU1_P; case => //.
  by move/sKn/(NltP nN) /cltNge; case.
have hu i j: i <c j -> j <c k -> Vf s i <c Vf s j.
  move => lij ljk; apply: hc => //; exact:(clt_ltT ljk kl1).
split => //.
set_extens t.
  move => tK; move: (hb _ (setU1_r n tK)) => [i ilk e1].
  move: ilk=> /(cltSleP kN) / cle_eqVlt; case => ee.
   by case: nK; rewrite - sk - ee - e1.
 by rewrite e1; apply: funI_i; apply/NltP.
move/funI_P => [i /(NltP kN) lik ->].
case /setU1_P: (hd _ (clt_ltT lik (cltS kN))) => // eq1.
by  move: (hc _ _ lik kl1); rewrite eq1 sk; case.
Qed.


Lemma nth_elt_dbl_prop2 E n (f:= (Lf (nth_elt_dbl E n) n n)):
  natp n -> sub E n ->
  inc f (permutations n) /\ E = Vfs f (cardinal E).
Proof.
move => nN seN.
set k := cardinal E.
have SKN: sub E Nat by move => t /seN /(NS_inc_nat nN).
move: (sub_smaller seN); rewrite -/k (card_card (CS_nat nN)) => lekn.
move: (NS_le_nat lekn nN) => kN.
move/setP_P: seN => seN. 
move: (nth_elt_dbl_prop nN seN) => [qa qb]; split => //.
have si :=  (proj33 lekn); have scE: sub k (source f) by rewrite /f; aw.
have ff: function f by apply: lf_function.
set_extens t.
move => tE. apply/(Vf_image_P ff scE).
  move: (nth_elt_surj SKN kN tE) => [i lik ->]; move/(NltP kN): (lik) => ik.
  by exists i => //; rewrite /f /nth_elt_dbl LfV//; [Ytac0 | apply: si ].
move/(Vf_image_P ff scE) => [i ik ->] .
move: (si _ ik)=> iin; move/(NltP kN): ik=> lik. 
rewrite /f /nth_elt_dbl LfV//; Ytac0.
apply:(nth_elt_inK (NS_lt_nat lik kN) SKN lik).
Qed.

(** partitions *)

Definition partition_with_pi_elements p E f :=
  [/\ domain f = domain p,
  (forall i, inc i (domain p) -> cardinal (Vg f i) = Vg p i) &
    partition_w_fam f E].

Definition partitions_pi p E :=
  Zo (gfunctions (domain p) (\Po E)) (partition_with_pi_elements p E).

Lemma  partitions_piP p E f:
  inc f (partitions_pi p E) <-> partition_with_pi_elements p E f.
Proof.
split; first by case /Zo_P. 
move=> h; apply: Zo_i =>//.
move: h => [p2 _ [p5 _ p7]].
set (g := triple (domain p) (\Po E) f).
have ->: (domain p = source g) by rewrite /g -p2; aw. 
have ->: (\Po E = target g) by rewrite /g; aw. 
have ->: (f = graph g) by rewrite /g; aw. 
apply: gfunctions_i; apply: function_pr =>// t.
move/(range_gP p5) => [x xdf ->]; apply /setP_P.
move => y; rewrite -p7 => hh; union_tac.
Qed.

Lemma fif_cardinal i p:
  finite_int_fam p -> inc i (domain p) -> cardinalp (Vg p i).
Proof. by move=> [fgp alip fdp]; fprops. Qed.

Lemma pip_prop0 p E f: partition_with_pi_elements p E f ->
  forall i, inc i (domain f) ->  sub (Vg f i) E.
Proof.
move=>  [df cVg [fgf duj ue]].
move=>i idp t tW; rewrite -ue; union_tac.
Qed.   

Lemma card_partitions1 p E:
  finite_int_fam p -> csum p = cardinal E ->
  nonempty (partitions_pi p E).
Proof. 
move=> fif.
move /card_eqP => [f [[injf [ff sjf]]] sf tg].
pose k i := (Vg p i) *s1 i.
have sx: forall i, inc i (domain p) -> sub (k i) (source f). 
  move=> i idp t tk; rewrite sf; apply /setUb_P1; ex_tac.
exists (Lg (domain p) (fun i => Vfs f (k i))); apply /partitions_piP.
split; first by aw.
  move=> i idp; rewrite /k LgV//.
  rewrite -{2} (card_card (fif_cardinal fif idp)).
  by rewrite (cardinal_image (sx _ idp) injf) cardinal_indexed.
split; first fprops.
  apply: mutually_disjoint_prop; aw.
  move=> i j y idp jdp; rewrite !LgV//.
  move: (sx _ idp)(sx _ jdp)=> p1 p2.
  move => /(Vf_image_P ff (sx _ idp)) [u uki Wu].
  move => /(Vf_image_P ff (sx _ jdp)) [v vkj Wv].
  rewrite Wv in Wu.
  have uv:=(proj2 injf _ _  (p2 _ vkj) (p1 _ uki) Wu).
  move: uki vkj; rewrite uv /k.
  by move /indexed_P => [_ _ <-] /indexed_P [_ _ <-].
rewrite -tg;set_extens x.
  move /setUb_P; aw; move=> [y yd]; move: (sx _ yd) => aux; rewrite LgV//.
  move=> /(Vf_image_P ff aux) [u uk ->];  Wtac.
move=> xtf; move: (sjf _ xtf)=> [y ysf Wy].
move: ysf; rewrite sf; move /disjointU_P=> [pa pb pc].
apply /setUb_P1;ex_tac; apply  /(Vf_image_P ff (sx _ pa)). 
by exists y => //; apply /indexed_P.
Qed.

Definition partitions_aux f g:=
  Lg (domain f) (fun i => Vfs g (Vg f i)).

Lemma card_partitions3 p E f g:
  partition_with_pi_elements p E f -> inc g  (permutations E) ->
  inc (partitions_aux f g) (partitions_pi p E).
Proof.
move=> pip gp.
apply /partitions_piP.
move: gp => /Zo_P [/functionsP [fg sg tg [ig sjg]]].
have Ha:forall u, inc u (domain f) -> sub (Vg f u) (source g).
  rewrite sg; apply: (pip_prop0 pip).
move: pip => [df cVg [fgf duj ue]].
hnf; rewrite / partitions_aux; saw.
  rewrite df;move=> i idp; rewrite LgV //- (cVg _ idp) ; symmetry.
  apply /card_eqP/Eq_restriction1 =>//; apply: Ha =>//; ue.
split;fprops.
  apply: mutually_disjoint_prop=>//; aw => i j y idp jdp; rewrite !LgV//.
  move: (Ha _ idp) (Ha _ jdp)=> s1 s2.
  move=> /(Vf_image_P fg s1) [u ui Wu] /(Vf_image_P fg s2) [v vi Wv].
  have uv: u = v.
    move: ig => [_ ig]; rewrite Wv in Wu;apply: ig; fprops.
  case: (duj _ _  idp jdp) => //; rewrite /disjoint => ns.
  rewrite -uv in vi; empty_tac1 u.
rewrite -tg;set_extens x.
  move /setUb_P1 => [y ydp].
  move /(Vf_image_P fg (Ha _ ydp)) => [u ua ->]; Wtac; exact: (Ha _ ydp).
move=> xtg; move: ((proj2 sjg) _ xtg)=> [y ysf Wy].
move: ysf; rewrite sg -ue;move=> /setUb_P [t tf etc].
apply /setUb_P1; ex_tac; apply /(Vf_image_P fg (Ha _ tf)); ex_tac.
Qed.

Lemma card_partitions4 p E f:
  finite_int_fam p -> csum p = cardinal E ->
  partition_with_pi_elements p E f ->
  surjection (Lf (partitions_aux f)
    (permutations E) (partitions_pi p E)).
Proof. 
move=>  fip spE [df cVg pfa];move:(pfa)=>  [fgf duj ue].
set phi:=Lf _ _ _. 
apply: lf_surjective; first by move=> g; apply: card_partitions3.  
have Ha:finite_set E by hnf;rewrite - spE; apply /NatP /finite_sum_finite.
move=> y /partitions_piP [dy cVy [fgy dujy uey]].
pose ha i := equipotent_ex (Vg f i) (Vg y i).
have hap: forall i, inc i (domain p) -> bijection_prop (ha i) (Vg f i) (Vg y i).
   move=> i idp; apply: equipotent_ex_pr.
   by apply /card_eqP; rewrite (cVg _ idp) (cVy _ idp).
pose h i :=  Lf (Vf (ha i))  (Vg f i) E.
have ta1:forall i, inc i (domain p) -> lf_axiom (Vf (ha i)) (Vg f i) E.
  move=> i idp z zW. 
  move: (hap _ idp)=> [[[fh _] _] sh th].
  rewrite - sh in zW;move: (Vf_target fh zW); rewrite th -uey.
  move=> h1; apply /setUb_P; exists i => //; ue.
have fp1:(forall i, inc i (domain f) -> function_prop (h i)  (Vg f i) E).
  rewrite  df /h=> i idp; saw; apply: lf_function; apply: ta1 =>//.
rewrite -df in hap.
move: (extension_partition1 pfa fp1). 
set g := common_ext _ _ _; move=> [[fg sg tg] extg].
have injg: injection g.
  split=> //; move=> u v.
  rewrite sg -ue; move=> /setUb_P [u' u'd Vu'] /setUb_P [v' v'd Vv'].
  have pu :  Vf g u = Vf (ha u') u.
    move: (extg _ u'd)  => [p1 p2 ->] //;rewrite  /h LfV//; apply: ta1; ue.
  have pv:  Vf g v = Vf (ha v') v.
    move: (extg _ v'd)=> [p1 p2 -> ] //; rewrite  /h LfV//; apply: ta1; ue.
  move=> eq; suff:u' = v'.
    move: (hap _ u'd) => [[[_ ih] _] sa _] aux.
    by rewrite sa in ih; apply: ih =>//; rewrite - ? pu ? aux // eq pv.
  case: (duj _ _ u'd v'd) =>// dj.
  have Wu: (inc (Vf g u) (Vg y u')). 
    rewrite pu; move: (hap _ u'd) => [[fh _] sa <-]; Wtac; fct_tac.
  have Wv: (inc (Vf g v) (Vg y v')).
    rewrite pv; move: (hap _ v'd) => [[fh _] sa <-]; Wtac; fct_tac.
  hnf in dujy; rewrite dy  -df in dujy.
  case: (dujy _ _ u'd v'd) =>// h1; rewrite eq in Wu; empty_tac1 (Vf g v).
have pg: inc g (permutations E) by apply: permutation_if_inj.
ex_tac; symmetry.
rewrite /partitions_aux; apply: fgraph_exten =>//; [ fprops |  aw; ue|].
aw; move=> x xdf /=; rewrite LgV//.
move: (hap _ xdf) => [bha sha tha].
move: (fp1 _ xdf) (extg _ xdf) => [fh sh th] [p2a _ p2c].
have p3 : forall i, inc i (Vg f x) -> Vf g i  = Vf (ha x) i.
  move=> i ins; rewrite (p2c _ ins) /h LfV//; apply: ta1 =>//; ue.
rewrite -tha.
set_extens u.
   move /(Vf_image_P fg p2a)=> [i ins ->]; rewrite  (p3 _ ins); Wtac;fct_tac.
move: bha => [iha sjha] ut.
move: (proj2 sjha _ ut)=> [v vs ->].
rewrite sha in vs; rewrite  - (p3 _ vs);  apply /(Vf_image_P fg p2a); ex_tac.
Qed.

Lemma card_partitions5P p E f g h:
  finite_int_fam p -> csum p = cardinal E ->
  partition_with_pi_elements p E f ->
  inc h (permutations E) -> inc g (permutations E) ->
 ( (partitions_aux f g = partitions_aux f h) <->
  (forall i, inc i (domain p) ->
      Vfs ( (inverse_fun h) \co g)  (Vg f i) = (Vg f i))).
Proof. 
move=> fip spE pip; move: (pip_prop0 pip)=> Ht.
move: pip => [df cVg [fgf duj ue]].
move => /Zo_P [] /functionsP [fh sh th] [inh [_ sjh]].
move => /Zo_P [] /functionsP [fg sg tg] bg.
have fih: function (inverse_fun h) by apply: bijective_inv_f. 
have cih: (inverse_fun h) \coP g by saw; ue.
have fcih : function ((inverse_fun h) \co g) by fct_tac. 
rewrite -df; split.
  move=> eq i idp; move: (f_equal (Vg ^~ i) eq);rewrite /partitions_aux !LgV//.
  move=> eql;rewrite /Vfs/inverse_fun/compose; aw.
  set_extens x. 
    move /dirim_P => [y yW /compg_pP [z pa /igraph_pP pb]].
    have : inc z (Vfs g (Vg f i)) by apply /dirim_P; ex_tac.
    rewrite eql; move /dirim_P =>  [x' x'Vf Jg2].
    by rewrite (injective_pr3 inh pb Jg2).
  move=> xW.
  have xsh: inc x (source h) by rewrite sh; apply: (Ht _ idp).
  have : (inc (Vf h x) (Vfs h (Vg f i))).
     apply /dirim_P; ex_tac; Wtac.
  rewrite -eql; move /dirim_P => [x' x'Vf Jg].
  apply /dirim_P; ex_tac; apply /compg_pP; ex_tac; apply /igraph_pP;Wtac.
move=> aux; apply: Lg_exten.
move=> i xdp; move: (aux _ xdp) => aux'.
set_extens x. 
  move /(dirim_P) => [y yVf Jg].
  have xt:inc x (target h) 
     by rewrite th -tg ;apply: (p2graph_target fg Jg). 
  move: (p1graph_source fg Jg) =>ys.
  move: (sjh _ xt)=> [z zs Wz].
  have p2: inc (J z x) (graph h) by rewrite Wz;apply: Vf_pr3 =>//.
  apply /dirim_P; ex_tac; rewrite -(aux _ xdp).
  apply /dirim_P; exists y => //; rewrite  corresp_g; apply /compg_pP.
  by exists x=> //; rewrite /inverse_fun; aw; apply /igraph_pP.
rewrite -{1} aux'/Vfs/compose /inverse_fun.
rewrite !corresp_g; move /(dirim_P)=> [u] /(dirim_P) [v Jg].
move /compg_pP =>[w pa /igraph_pP pb] pc.
apply /dirim_P; ex_tac; rewrite - (fgraph_pr _ pb pc); fprops.
Qed.

Lemma card_partitions6 p E f h:
  finite_int_fam p -> csum p = cardinal E ->
  partition_with_pi_elements p E f ->
  inc h (permutations E) ->
  lf_axiom (fun g=> Lg (domain p)(fun i=>  (restriction2 
    ((inverse_fun h) \co g) 
    (Vg f i) (Vg f i))))
  (Zo  (permutations E) 
    (fun g => (partitions_aux f g = partitions_aux f h)))
  (productb (Lg (domain p)(fun i=> (permutations (Vg f i))))).
Proof.
move=> fip spE pip hp g; move: (pip_prop0 pip)=> Ht.
move: (pip) => [df cVg [fgf duj ue]].
move /Zo_P => [gp eql]; apply /setXb_P; fprops;split;aww.
move=> i idp; rewrite !LgV//.
move: eql; move /(card_partitions5P fip spE pip hp gp) => eql.
move: (eql _  idp) => ic; clear eql.
move: hp gp => /Zo_P [] /functionsP [fh sh th] bh.
move=> /Zo_P [] /functionsP [fg sg tg] bg.
have fih: function (inverse_fun h) by apply: bijective_inv_f. 
have cih: (inverse_fun h) \coP g by saw; ue.
have fcih : function ((inverse_fun h) \co g) by fct_tac.
set k:= restriction2 _ _ _.
have sk: source k = Vg f i by rewrite /k/restriction2; aw.
have tk: target k = Vg f i by rewrite /k/restriction2; aw.
rewrite df in Ht; move: (Ht _ idp) => Ht1.
have ra: (restriction2_axioms (compose (inverse_fun h) g) (Vg f i) (Vg f i)).
   hnf; saw; ue. 
have fk: (function k) by rewrite /k; apply: (proj31(restriction2_prop ra)).
apply:permutation_if_inj. 
- rewrite /finite_set;move: pip fip => [_ pip _] [hp _ ].
  by rewrite  (pip _ idp); apply/NatP; apply: hp.
- done.
split=>// x y; rewrite sk => xsk ysk.
rewrite /k restriction2_V //restriction2_V //.
move: (Ht1 _ xsk) (Ht1 _ ysk); rewrite - sg => xsg ysg.
rewrite !compfV// ;move => eq.
move: bg=> [[_ ig] _ ]; apply: (ig _ _ xsg ysg).
move: (inverse_bij_fb bh) => [[_ iih] _ ]. 
move:iih; aw; apply =>//; try (rewrite th -tg; Wtac).
Qed.

Lemma card_partitions7 p E f h:
  finite_int_fam p -> csum p = cardinal E ->
  partition_with_pi_elements p E f ->
  inc h (permutations E) ->
  bijection (Lf (fun g=> Lg (domain p)(fun i=> (restriction2 
    ((inverse_fun h) \co g) 
    (Vg f i) (Vg f i))))
  (Zo (permutations E) 
    (fun g => (partitions_aux f g = partitions_aux f h)))
  (productb (Lg (domain p)(fun i=> (permutations (Vg f i)))))).
Proof.
move=> fip spE pip hp; move: (pip_prop0 pip)=> sWE.
move: (pip) => [df cVg [fgf duj ue]]; move: (proj33 pip) => pfa.
rewrite df in sWE.
set ww:=Lf _ _ _.
move: (card_partitions6 fip spE pip hp) => ta.
move:(hp) => /Zo_P [] /functionsP [fh sh th] bh.
have bih: (bijection (inverse_fun h)) by apply: inverse_bij_fb. 
have fw: function ww by apply: lf_function.
have sw: surjection ww.
  split => // y.
  rewrite {1 2} /ww; aw; move /setXb_P; aw; move=> [fgy dy yp].
  have yp': (forall i, inc i (domain p) ->   
      (bijection_prop (Vg y i) (Vg f i) (Vg f i))).
   by move=> i idp;move: (yp _ idp); rewrite LgV//;move => /Zo_P [/functionsP [? ? ?] ?]. 
  have ta1: (forall i, inc i (domain p) -> lf_axiom (Vf (Vg y i)) (Vg f i) E). 
    move=> i idp z zW; move: (yp' _ idp)=> [bha sha tha].  
    apply: (sWE _ idp); rewrite -tha;Wtac; fct_tac.
  pose hb i :=  Lf (Vf (Vg y i))  (Vg f i) E.
  have Hw:forall i, inc i (domain f) -> function_prop (hb i) (Vg f i) E. 
    rewrite df; move => i ip; rewrite /hb /function_prop lf_source lf_target.
    split => //; apply: lf_function;apply: ta1 =>//.
  move: (extension_partition1 pfa Hw). 
  set g := common_ext _ _ _; move => [[fg sg tg] alag].
  have ijg: injection g.
    split=>// u v; rewrite sg => uE vE.
    move: uE vE;rewrite -ue; move=> /setUb_P  [a adf ua] /setUb_P [b bdf vb].
    move: (alag _ adf)(alag _ bdf) => [p1 p2 p3] [q1 q2 q3].
    have ap: inc a (domain p) by ue. 
    have bp: inc b (domain p) by ue. 
    move : (ta1 _ ap) (ta1 _ bp) => ta2 ta3.
    rewrite (p3 _ ua)(q3 _ vb) /hb (LfV ta2 ua) (LfV ta3 vb).
    move: (yp' _ ap) (yp' _ bp)=> [[[_ iha] xx] sha tha] [yy shb thb].
    case: (duj _ _ adf bdf).
      move=> ab; rewrite -ab in vb; rewrite -ab.
      apply: iha; rewrite sha //.
    move=> h1 h2; empty_tac1 (Vf (Vg y a) u).
    - rewrite /Vf in tha;rewrite -tha; Wtac; fct_tac.
    - rewrite /Vf in thb;rewrite h2 -thb; Wtac; fct_tac.
  have gp: inc g (permutations E).
    apply:permutation_if_inj => //.
    apply /NatP; rewrite - spE; apply: finite_sum_finite =>//.
  move/permutationsP:(gp) => [bg _ _].
  have pa:forall i v, inc i(domain p) -> inc v (Vg f i) ->
     Vf g v  = Vf (Vg y i) v.
    rewrite -df;move=> i v idp; move: (alag _ idp).  
    rewrite /agrees_on; move => [s1 s2 aux].
    move=> vW;move:(aux _ vW); rewrite /hb LfV; [done | apply: ta1;ue| done ].
  have pb:forall i v, inc i (domain p)-> inc v (Vg f i) -> inc (Vf g v)(Vg f i).
    move=> i v ip iv; rewrite (pa _ _ ip iv). 
    move: (yp' _ ip) => [bha sha tha]; Wtac; fct_tac.
  set (t:= h \co g).
  have pt: inc t (permutations E) by apply (permutation_Sc hp gp).
  set z:=Zo _ _.
  have xz:inc t z.
    apply: Zo_i => //.
    rewrite /partitions_aux df; apply: Lg_exten.
    move=> i idp /=; set_extens u; aw.
      move /dirim_P => [a ai]; rewrite /t /compose; aw.
      move /compg_pP =>  [b Jg1 Jg2]; apply /dirim_P; ex_tac.
      by move: (Vf_pr fg Jg1) => ->; apply: pb.
    move=> /dirim_P [a asVf Jg]. 
    have atg: inc a (target g) by rewrite tg; apply: (sWE _ idp).
    move: (bg) => [_ sjg]; move: ((proj2 sjg) _ atg)  => [b bsg Wb].
    move: (bsg); rewrite sg; rewrite -ue; move /setUb_P => [j jd aw].
    apply /dirim_P.
    rewrite -df in idp pb; case: (duj _ _ idp jd) => di.
      rewrite -di in aw; ex_tac.
      rewrite /t /compose; aw; apply /compg_pP; ex_tac; rewrite Wb; Wtac.
    empty_tac1 a; rewrite Wb;apply: (pb _ _ jd aw). 
  ex_tac; rewrite (LfV ta xz). 
  rewrite /t (permutation_lK hp gp).
  symmetry;apply: fgraph_exten;aw; fprops => x xdp; aw.
  move: (sWE _ xdp)=> Wf.
  have ra:  (restriction2_axioms g (Vg f x) (Vg f x)).
   have ssg: sub (Vg f x) (source g) by rewrite sg.
   have stg: sub (Vg f x) (target g) by rewrite tg.
   split => //; move=> u /(Vf_image_P fg ssg) [v vW ->]; apply: (pb _ _ xdp vW).
  move : (yp' _ xdp) => [bha sha tha].
  rewrite LgV//; apply: function_exten.
  - by apply: (proj31 (restriction2_prop ra)).
  - fct_tac.
  - by rewrite /restriction2 sha corresp_s.
  - by rewrite /restriction2 tha corresp_t.
  - rewrite /restriction2; aw; move=> u uW /=; rewrite restriction2_V //.
    by rewrite (pa _ _ xdp uW).
split=>//; split =>//.
rewrite /ww lf_source=> x y xS yS; rewrite (LfV ta xS) (LfV ta yS).
move: xS yS => /Zo_P [xs eq1] /Zo_P [ys eq2].
move: eq1 => /(card_partitions5P fip spE pip hp xs).
move: eq2 => /(card_partitions5P fip spE pip hp ys).
set xi:=  _ \co x; set yi:= _ \co y => eq2 eq1 eq.
suff: xi = yi.
  rewrite /xi /yi;move => eqi; move: (f_equal (compose h) eqi).
  by rewrite (permutation_lK' hp xs)(permutation_lK' hp ys).
move:(permutation_Si hp) => hp'.
move:(permutation_Sc hp' xs) => /permutationsP[ /proj1/proj1 bxi  sxi txi].
move:(permutation_Sc hp' ys) => /permutationsP[ /proj1/proj1 byi  syi tyi].
apply: (function_exten bxi byi).
  by rewrite sxi syi.
  by rewrite txi tyi.
rewrite sxi -ue;move=> u; move /setUb_P; rewrite df; move=> [i ip iW].
move: (f_equal (Vg ^~i) eq); rewrite !LgV// => eq3.
have ra:restriction2_axioms xi (Vg f i) (Vg f i).
  split => //; last (by rewrite eq1; fprops);
  rewrite ?sxi ?txi;apply: (sWE _ ip).
have rb:restriction2_axioms yi (Vg f i) (Vg f i).
  split => //; last (by rewrite eq2; fprops);
    rewrite ? syi ? tyi; apply: (sWE _ ip).
move: (f_equal (Vf ^~u) eq3);rewrite restriction2_V // restriction2_V //.
Qed.

Theorem card_partitions p E
   (num:= factorial (cardinal E)) 
   (den := cprodb  (domain p) (fun z => factorial (Vg p z))):
  finite_int_fam p -> csum p = cardinal E ->
        [/\ num = cardinal (partitions_pi p E) *c den,
        natp num, natp den, den <> \0c &
        finite_set (partitions_pi p E)].
Proof.
move => fip spe.
move: (card_partitions1 fip spe)=> [h hp].
have Hb: finite_set E.
  by hnf; rewrite - spe; apply /NatP; apply: finite_sum_finite=> //.
have numN: natp num  by rewrite /num; apply: NS_factorial; apply /NatP; aw.
have ndenN: natp den.
  move: fip=> [p2 p3].  
  rewrite /den;apply: finite_product_finite =>//.
  by hnf; saw; hnf; aw => i idp; rewrite LgV//; apply: NS_factorial; apply: p2.
have nd:den <> \0c. 
  move: fip=> [p2 p3]. 
  apply /cprod_nzP; hnf;aw => i idp; rewrite LgV//; apply: factorial_nz; apply: p2=>//.
rewrite /finite_set; set aux:= cardinal _. 
suff: num = aux *c den.
  move => eql; split => //.
  by apply /NatP /(NS_in_product (CS_cardinal (partitions_pi p E)) nd);ue.
move: hp => /Zo_P [hfpp pip].
move:(card_partitions4 fip spe pip).
set phi:= Lf _ _ _; move=> sjphi. 
suff phip: forall x, inc x (target phi) ->
    cardinal (Vfi1 phi x) = den. 
  move:  sjphi=> [fphi _].
  move:(shepherd_principle  fphi phip). 
  rewrite /phi lf_source lf_target card_permutations //.
move=> x xt.
move:((proj2 sjphi) _ xt) => [y ys yw].
move: ys; rewrite {1}/ phi; aw => yp.
move: (card_bijection (card_partitions7 fip spe pip yp)).
rewrite lf_source lf_target;  congr (cardinal _ = _); last first.
  apply: Eqc_setXb; split;aww  => i idp; rewrite !LgV//.
  move: pip (proj1 fip _ idp)=>[p1 p2 [p3 _ _]] /NatP fv.
  rewrite card_permutations /finite_set  (p2 _ idp) // card_card //.
  by apply:CS_factorial.
have Ha:lf_axiom (fun g =>
     (partitions_aux h g)) (permutations E) (partitions_pi p E).
  by move => g gp; apply: card_partitions3.
have fphi: function phi by fct_tac. 
set_extens t.
  move /Zo_P => [pa pb].
  apply: (iim_fun_set1_i fphi); rewrite /phi; aw; trivial.
  by rewrite yw /phi ! LfV.
case /(iim_fun_set1_P _ fphi); rewrite /phi lf_source => ta.
by rewrite LfV// => tb; apply: Zo_i => //; rewrite - tb yw /phi LfV.
Qed.

Theorem card_partitions_bis p E:
  finite_int_fam p -> csum p = cardinal E ->
  cardinal (partitions_pi p E) = 
  (factorial (cardinal E)) %/c
           (cprodb (domain p) (fun z => factorial (Vg p z))).
Proof. 
move=>  h1 h2.
move: (card_partitions h1 h2) => [p1 p2 p3 p4] /NatP p5.
by rewrite p1 cprodC; symmetry; apply: cdivides_pr4.
Qed.

Lemma card_partitions_p2 E m p
   (num := factorial (m +c p))
   (den := (factorial m) *c (factorial p))
   (x := cardinal (partitions_pi (variantLc m p) E)):
  natp m -> natp p -> cardinal E = (m +c p) ->
   [/\ natp x, num = x *c den,natp num, natp den & den <> \0c].
Proof.
move=> mN pN cE.
set P:= variantLc m p.
have h1: finite_int_fam P.
  rewrite /P;split;fprops.
  by hnf; aw; move=> i it; try_lvariant it.
  aw;apply: set2_finite.
have p2: csum P = cardinal E.
  symmetry;rewrite cE /csum2/csum; fprops.
move: (card_partitions h1 p2); simpl.
set y:= cprodb _ _.
have -> : den = y.
  rewrite /den/cprod2/y/P; aw; apply:cprodb_exten.
  move=> xx xtp /=; try_lvariant xtp; fprops.
rewrite cE; move=> [r1 r2 r3 r4 r5];split;fprops.
Qed.


(** Binomial coefficient *)

Definition binom n m :=
  Vg (induction_term
      (fun _ T: Set => Lg Nat (fun z => variant \0c \1c
          (Vg T z +c Vg T (cpred z)) z))
       (Lg Nat (variant \0c \1c \0c))
       n) m.

Lemma binom00: binom \0c \0c = \1c.
Proof.
rewrite /binom induction_term0 /variant LgV//; [ by Ytac0 | apply:NS0 ].
Qed.

Lemma binom0Sm m: natp m -> 
  binom \0c (csucc m) = \0c.
Proof.
move=> mN; have snz := (@succ_nz m).
by rewrite /binom /variant induction_term0 LgV//; [ Ytac0 | apply: NS_succ].
Qed.

Lemma binomSn0 n: natp n ->  binom (csucc n) \0c = \1c.
Proof.
move: NS0 => zn nN; rewrite /binom  /variant induction_terms // LgV//.
by Ytac0.
Qed.

Lemma binomSnSm n m: natp n -> natp m ->
  binom (csucc n) (csucc m) = (binom n (csucc m)) +c (binom n m).
Proof.
move=> nN mN.
have snz := (@succ_nz m); have smN:= NS_succ mN.
rewrite /binom /variant induction_terms //  LgV//.
Ytac0; rewrite cpred_pr1 //; fprops. 
Qed.

Lemma NS_binom n m: natp n -> natp m -> natp (binom n m).
Proof.
move=> nN; move: n nN m; apply: Nat_induction.
  apply: Nat_induction; first by rewrite  binom00=>//; fprops.
  move => n nN _; rewrite  binom0Sm; fprops.
move => n nN hrec; apply: Nat_induction; first by rewrite  binomSn0; fprops.
move => p pN bN; rewrite  binomSnSm; fprops.
Qed.

Lemma binom_alt_pr n m: natp n -> natp m ->
  (binom n m) *c  ((factorial m) *c (factorial (n -c m))) = 
  Yo (m <=c n) (factorial n) \0c.
Proof. 
move: n m.
pose Bi n m := (binom n m) *c (factorial m *c (factorial (n -c m))).
have ba4:  forall n m, natp n -> natp m -> Bi (csucc n) (csucc m)= 
    ((Bi n (csucc m)) *c (Yo (n <=c m) \1c (n -c m)))
   +c (Bi n m *c csucc m). 
  move=> n m nN mN.
  rewrite /Bi binomSnSm // cdiff_pr6 // cprodDl.
  set aux := (factorial (csucc m)) *c (factorial (n -c m)).
  set A:= (binom n (csucc m)) *c aux.
  suff: A = (Bi n (csucc m)) *c (Yo (n <=c m) \1c (n -c m)).
    move => ->; congr (_ +c _); rewrite - cprodA; congr (_ *c _).
    by rewrite (cprodC (factorial m) _) - cprodA -(factorial_succ mN) cprodC.
  rewrite /A  /Bi  /aux - 2! cprodA; apply:f_equal; apply:f_equal.
  case: (p_or_not_p (n <=c m)) => le; Ytac0.
    rewrite (Nprod1r (NS_factorial (NS_diff (csucc m) nN))).
    by rewrite (cdiff_wrong (cleT le (cleS mN))) (cdiff_wrong le).
  case: (NleT_el nN mN) => // /(cleSltP mN) /(csucc_diff nN mN) s.
  rewrite s factorial_succ; fprops.
move=> n m nN mN. 
rewrite  -/(Bi n m); move: n nN m mN; apply: Nat_induction.
  move=> m mN.
  rewrite /Bi cdiff_0n factorial0 (Nprod1r (NS_factorial mN)).
  move: m mN; apply: Nat_induction.
    rewrite binom00 factorial0 (cprod1l CS1) Y_true; fprops.
  move=> p pN  aux; Ytac h; first by move: (cleNgt h (succ_positive p)).
  by rewrite binom0Sm // cprod0l.
move=> N NN rN; apply: Nat_induction.
  move: (NS_succ NN) => sN; move: (NS_factorial sN) (cle0n sN) => fN sp.
  by rewrite /Bi (binomSn0 NN)(cdiff_n0 sN)factorial0 !(Nprod1l fN) Y_true.
move => p pN bN.
rewrite (ba4 _ _ NN pN) (rN _ pN)(rN _ (NS_succ pN)) factorial_succ //.
case: (NleT_el  (NS_succ pN) NN) => c1.
  have lepN:=(cleT (cleS pN) c1).
  case: (p_or_not_p (N <=c p)) => h; first case:(cleNgt (cleT c1 h) (cltS pN)).
  rewrite (Y_true c1)(Y_true lepN)(Y_true (cleT c1 (cleS NN))) (Y_false h).
  by rewrite  - cprodDr (Nsucc_rw pN) (Nsucc_rw NN) csumA (cdiff_rpr lepN).
move /(cltSleP pN): (c1) => c2.
rewrite (Y_false (cltNge c1)) cprod0l.
case: (equal_or_not N p) => epN.
  rewrite - epN (Y_true (cleR (CS_nat NN))) csum0l ? Y_true; fprops.
move:(cltNge (conj c2 epN)) => c3.
move /(cleSSP (proj32 c2) (proj31 c2)): (c3) => c4.
by Ytac0; Ytac0; rewrite cprod0l // (Nsum0l NS0).
Qed.

Lemma binom_bad n m: natp n -> natp m -> 
  n <c m -> binom n m = \0c.
Proof.
move=> nN mN h; move: (factorial_nz mN) (factorial_nz (NS_diff m nN))=> sa sb.
move: (binom_alt_pr nN mN).
by rewrite (Y_false (cltNge h)) => /cprod2_eq0; case => //;case/cprod2_eq0. 
Qed.

Lemma binom_good n m: natp n -> natp m -> 
  m <=c n ->
  (binom n m) *c ((factorial m) *c (factorial (n -c m))) = (factorial n).
Proof. by move=> nN mN h; move: (binom_alt_pr nN mN); Ytac0. Qed.


Lemma binom_ffact n m : natp n -> natp m ->
  binom n m *c (factorial m)  = n ^_c m.
Proof.
move => nN mN.
case: (NleT_el mN nN) => cnm; last first.
  by rewrite (binom_bad nN mN cnm) (ffact_small mN cnm) cprod0l.
move:(binom_good nN mN cnm).
rewrite - (ffact_fact nN mN cnm) cprodA.
have ha := (NS_factorial (NS_diff m nN)).
have hb := (NS_prod (NS_binom nN mN)  (NS_factorial mN)).
apply: (cprod_eq2r ha  hb (NS_ffact nN mN) (factorial_nz (NS_diff m nN))).
Qed.

Lemma binom_ffactd n m : natp n -> natp m ->
  binom n m = n ^_c m %/c (factorial m).
Proof.
move => nN mN.
have ha := (NS_factorial mN).
have hb := NS_binom nN mN.
by rewrite -(binom_ffact nN mN) cprodC (cdivides_pr4  ha hb (factorial_nz mN)).
Qed.

Lemma binom_pr0 n p
   (num := factorial n)
   (den:=  (factorial p) *c (factorial (n -c p))):
   natp n -> natp p -> p <=c n ->
   den %|c num /\ binom n p = num %/c den.
Proof.
move=> nN pN h; move: (binom_good nN pN h).
have nuN: natp num by apply: NS_factorial =>//.
have deN: natp den by apply: NS_prod;apply: NS_factorial; fprops.
have dnz: den <>  \0c.
   rewrite /den; apply: cprod2_nz; apply: factorial_nz; fprops. 
have bN: natp (binom n p) by apply: NS_binom =>//.
rewrite cprodC -/num  => <-.
by split; [ apply:cdivides_pr1 |rewrite cdivides_pr4 ].
Qed.

Lemma binom_pr1 n p: natp n -> natp p -> 
  p <=c n ->
  binom n p = (factorial n) %/c ((factorial p) *c (factorial (n -c p))).
Proof.
by move=> nN pN h; move: (binom_pr0 nN pN h)=> [_].
Qed.

Lemma binom_symmetric n p: natp n -> 
  p <=c n -> binom n p = binom n (n -c p).
Proof. 
move => nN h.
move: (NS_le_nat h nN) => pN.
move: (cdiff_ab_le_a p (CS_nat nN)) => aux.
rewrite (binom_pr1 nN pN h) cprodC (binom_pr1 nN (NS_diff p nN) aux).  
rewrite double_diff //; apply: le_minus. 
Qed.

Lemma binom_symmetric2 n m: natp n ->  natp m ->
    binom (n +c m) m = binom (n +c m) n.
Proof.
move => nN mN.
rewrite csumC (binom_symmetric (NS_sum mN nN) (Nsum_M0le n mN)). 
rewrite csumC (cdiff_pr1 nN mN) //.
Qed.

Lemma binom0 n: natp n -> binom n \0c = \1c.
Proof.  
move=> nN.
case: (equal_or_not n \0c) => nz; first by rewrite nz binom00.
move: (cpred_pr nN nz)=> [pN ->]; rewrite binomSn0 //.
Qed.

Lemma binom1 n: natp n -> binom n \1c = n.
Proof.
move: n; rewrite - succ_zero;apply: Nat_induction.  
  rewrite binom0Sm; fprops.
move=> p pN r.
by rewrite (binomSnSm pN NS0) r (binom0 pN) (Nsucc_rw pN).
Qed.

Lemma binom2a n: natp n ->
  \2c *c (binom (csucc n) \2c) = n *c (csucc  n).
Proof. 
move:n ; rewrite -{2} succ_one; apply: Nat_induction.  
  rewrite cprod0l (binomSnSm NS0 NS1) (binom0Sm NS1) (binom1 NS0).
  by rewrite (Nsum0r NS0) cprod0r.    
move=> n nN r; move: (NS_succ nN) => sN.
rewrite (binomSnSm sN NS1) cprodDr r (binom1 sN) - cprodDl cprodC.
by rewrite - csum_11 (Nsucc_rw sN) (Nsucc_rw nN) csumA.
Qed.

Lemma binom2 n: natp n ->
  binom (csucc n) \2c = (n *c (csucc n)) %/c \2c.
Proof. 
move=> nN; move: (NS_succ nN) => sN.
apply: (cdivides_pr2 (NS_prod nN sN) NS2 (NS_binom sN NS2) card2_nz).   
by rewrite (binom2a nN). 
Qed.

Lemma binom_nn n: natp n -> binom n n = \1c.
Proof. 
move=> nN.
rewrite (binom_symmetric nN (cleR (CS_nat nN))) cdiff_nn binom0 =>//.
Qed.

Lemma binom_pr3 n p: natp n -> natp p  -> 
  p <=c n -> binom n p <> \0c.
Proof.
move=> nN pN h bz; move: (binom_good nN pN h).
rewrite bz cprod0l => fz.
by case: (factorial_nz nN).
Qed.


Lemma binom_monotone1 k n m:
  natp k -> natp n -> natp m ->
  k <> \0c -> k <=c (csucc n) -> n <c m ->
  (binom n k) <c (binom m k).
Proof. 
move: k n m.
have : forall k n, natp k -> natp n -> 
  k <> \0c -> k <=c (csucc n) -> (binom n k) <c (binom (csucc n) k).
  move => k n kN nN  r1 r2.
  move: (cpred_pr kN r1) => [pN ps].
  rewrite {2} ps (binomSnSm nN pN) -ps.
  apply: (csum_M0lt (NS_binom nN kN));apply: binom_pr3 =>//.
  apply /(cleSSP (CS_nat pN)  (CS_nat nN)); rewrite  -ps//.
move=> aux k n m kN nN mN  r1 r2 r3.
move/(cleSltP nN): r3 => r6.
have r8:= cleR (CS_nat mN).
pose r p := (binom n k) <c (binom p k).
apply: (Nat_induction3 (r:=r) (NS_succ nN) mN (aux _ _ kN nN r1 r2) _ r6 r8).
move => n' r4 r5 r7;apply:(clt_ltT r7).
apply: (aux _ _ kN (NS_lt_nat r5 mN) r1).
exact:(cleT (cleT r2 r4) (cleS0 (proj32 r4))). 
Qed.

Lemma binom_monotone2 k n m:
  natp k -> natp n -> natp m ->
  k <> \0c -> k <=c (csucc n) ->  k <=c (csucc m) ->
  (n <c m <-> (binom n k) <c (binom m k)).
Proof. 
move=>  kN nN mN r1 r2 r3.
split; first by  apply: binom_monotone1.
case: (cleT_el (CS_nat mN)  (CS_nat nN)) => // mn [ble bne].
case: (equal_or_not m n) => nm; first by case: bne; rewrite nm.
have bgt: (binom m k) <c (binom n k) by apply: binom_monotone1.
case:(cltNge bgt ble).
Qed.


Lemma mul_Sm_binom m n : natp n -> natp m ->
  csucc m *c  binom m n = csucc n *c binom (csucc m) (csucc n).
Proof.
move => nN mN; move: m mN n nN ; apply: Nat_induction.
  move => n nN; case: (czero_dichot (CS_nat nN)) => nz.
    by rewrite nz succ_zero (binom_nn NS0) (binom_nn NS1). 
  rewrite (binom_bad NS0 nN nz) (binom_bad); fprops; last by apply: cltSS.
  by rewrite !cprod0r.
move => m mN Hrec n nN.
have smN := (NS_succ mN).
case: (czero_dichot (CS_nat nN)) => nz.
  by rewrite nz (binom0 smN) succ_zero (binom1 (NS_succ smN)) cprodC.
move: (cpred_pr nN (nesym (proj2 nz))); set k := cpred n; move => [kN ->].
move:  (NS_succ kN) => skN.
rewrite (cprod_Sn _ smN) {2} (binomSnSm mN kN) cprodDr (Hrec _ skN) (Hrec _ kN).
by rewrite csumCA - (cprod_Sn _ (NS_succ kN)) - cprodDr - (binomSnSm smN skN).
Qed.

Lemma mul_Sm_binom_1 n p : natp n -> natp p ->
  n *c (binom (n +c p) p) = (csucc p) *c binom (n+c p) (csucc p).
Proof.
move => nN pN.
case: (equal_or_not n \0c) => nz.
  rewrite nz (csum0l (CS_nat pN)) (binom_bad pN (NS_succ  pN) (cltS pN)).
  by rewrite cprod0l cprod0r.
rewrite (binom_symmetric2 nN pN).
move: (cpred_pr nN nz); set k := cpred n; move => [kN ->]. 
rewrite (csum_Sn _ kN).
rewrite - (mul_Sm_binom kN (NS_sum kN pN)).
rewrite - (mul_Sm_binom pN (NS_sum kN pN)).
by rewrite (binom_symmetric2 kN pN).
Qed.
  
Lemma binom_rec1 n k: natp n -> k <=c n ->
  (n -c k) *c (binom n k) = (csucc k) *c binom n (csucc k).
Proof.
move => nN lkn; move: (NS_diff k nN) (NS_le_nat lkn nN) => ha hb. 
by rewrite - {2 3} (cdiff_pr lkn) csumC mul_Sm_binom_1. 
Qed.


Lemma binom_monotone3 n k: natp n -> k <=c n ->
  ( (binom n k) <=c binom n (csucc k)  <-> csucc (cdouble k) <=c n).
Proof.
move => nN lkn; move: (NS_diff k nN) (NS_le_nat lkn nN) => dN kN. 
have skN:= NS_succ kN.
have eq1:= (binom_rec1 nN lkn).
have aux: csucc k <=c n-c k <-> csucc (cdouble k) <=c n.
  rewrite cdoubleE - (csum_Sn _ kN) - {2} (cdiff_pr lkn) csumC.
  by split => hyp; [ apply: csum_Meqle|apply: (csum_le2l kN skN dN)].
move: (NS_binom nN kN)(NS_binom nN skN) => b1N b2N.
split.
  move => hyp;apply/aux. 
  move: (cprod_Meqle (n -c k) hyp); rewrite eq1.
  apply /(cprod_le2r b2N skN dN); apply: (binom_pr3 nN  skN).
  apply/(cleSltP kN); split => // ekn.
  move: hyp; rewrite ekn (binom_nn nN) (binom_bad nN (NS_succ nN) (cltS nN)).
  exact: (cltNge clt_01).
move/aux => hyp.
case: (equal_or_not (n -c k) \0c) => kn.
  by case: (cltNge(succ_positive k)); rewrite - kn.
apply: (cprod_le2l dN b1N b2N kn).
by rewrite eq1; apply:cprod_Mleeq.
Qed.

Lemma binom_monotone4 n k: natp n -> k <=c n ->
  ( (binom n k) <c binom n (csucc k)  <-> cdouble (csucc k) <=c n).
Proof.
move => nN lkn; move: (NS_diff k nN) (NS_le_nat lkn nN) => dN kN.
have skN:= NS_succ kN.
have eq1:= (binom_rec1 nN lkn).
have qa: natp (csucc (cdouble k)) by apply:NS_succ; apply:NS_double.
have: csucc (cdouble k) <c n <-> cdouble (csucc k) <=c n.
   rewrite (double_succ kN); apply: iff_sym; exact:(cleSltP qa).
have b1N: natp (binom n k) by apply: NS_binom.
have b2N: natp (binom n (csucc k))  by apply: NS_binom.
apply: iff_trans; split.
  move => [/(binom_monotone3 nN lkn) h neq]; split => // eq2.
  have eq3 :csucc k  = (n -c k).
    by rewrite - eq2 cdoubleE - (csum_Sn _ kN) cdiff_pr1.
  by case: neq; apply: (cprod_eq2l skN b1N b2N (@succ_nz _)); rewrite - eq1 eq3.
move => [/(binom_monotone3 nN lkn) le1 neq]; split => // eq2.
move/(strict_pos_P1 b1N): (binom_pr3 nN kN lkn) => lt1.
move: (nesym (proj2(clt_leT lt1 le1))) => bnz.
rewrite eq2 in eq1.
move:(cprod_eq2r b2N dN skN bnz eq1) => nk.
case: neq; rewrite -(cdiff_pr lkn) nk (csum_nS _ kN) csum_nn //. 
Qed.

Lemma binom_half_aux n: natp n -> oddp n ->
    binom n (chalf n) = binom n (csucc (chalf n)).
Proof.
move => nN no; move: (NS_half nN).
rewrite {2 4} (half_odd no); set k := chalf n => kN.
have ->: (csucc (cdouble k)) = (csucc k) +c k.
  by rewrite cdoubleE - (csum_Sn _ kN).
exact:  (binom_symmetric2 (NS_succ kN) kN).
Qed.

Lemma binom_max n k: natp n -> k <=c n ->
  (binom n k) <=c binom n (chalf n).
Proof.
move => nN lkn; move: (NS_half nN) => hN.
suff: forall k, k <c chalf n -> binom n k <=c binom n (chalf n).
  move => hyp.
  move: (NS_le_nat lkn nN) => kN.
  case: (NleT_ell hN kN) => sm.
  + rewrite sm; apply: cleR; apply:(CS_nat (NS_binom nN kN)).
  + case: (p_or_not_p (oddp n /\ k = csucc (chalf n)))=> sp.
      move: (binom_half_aux nN (proj1 sp)); rewrite - (proj2 sp) => ->.
      by apply:(cleR (CS_nat (NS_binom nN kN))).
    rewrite (binom_symmetric nN lkn); apply: hyp;apply:(cdiff_Mlt hN nN lkn).
    case: (p_or_not_p (evenp n)) => nev.
      apply: (cle_ltT _ (csum_Meqlt hN sm)).
      rewrite csum_nn -/(cdouble _) - (half_even nev);fprops.
   have on: oddp n by [].    
   rewrite {1} (half_odd  on) cdoubleE -(csum_nS _ hN).
   apply:(csum_Meqlt hN); split; [ by apply/cleSltP | fprops ].
  + by apply: hyp.  
clear k lkn.
move:{1 2 4 5} (chalf n) hN (cleR (CS_nat hN)).
apply: Nat_induction.
       by move => _ k /clt0.
move =>m mN Hrec mp k kl.
have cdm:  csucc (cdouble m) <=c n.
  apply: cleT (half_monotone2 (NS_succ mN) nN mp).
  by  rewrite (double_succ mN); apply: cleS; apply: NS_succ; apply: NS_double.
have lemn:= (cleT (cleT (cleS mN) mp) (cle_halfn_n nN)).
move/(binom_monotone3 nN lemn): cdm.
move/(cltSleP mN): kl => /cle_eqVlt; case; [ by move -> | move => lkm].
apply: cleT; exact: (Hrec (cleT (cleS mN) mp) k lkm).
Qed.


Lemma binom_monotone_max_arg n k (h := chalf n): natp n -> k <=c n ->
  ( (binom n k) = (binom n h) <-> (k = h \/ n -c k = h) ).
Proof.
move => nN lkn.
have hN:= (NS_half nN).
split; last first.
  case; move <- => //; exact: (binom_symmetric nN lkn).
wlog ll : k lkn/ (k <=c h).
  move => hyp; move: (NS_le_nat lkn nN) => kN.
  case:(NleT_el kN hN); first by apply: hyp.
  rewrite (binom_symmetric nN lkn) => lt1 eq1.
  have qa: n -c k <=c h.
    move/(cleSltP hN): lt1 => /(csum_Meqle (chalf n)) => le.
    apply:(cdiff_Mle hN kN); apply: (cleT _ le).
    rewrite  (csum_nS _ hN)  - cdoubleE.
   case: (cdouble_halfV nN) => <-; fprops.
  move: (cleT qa (cle_halfn_n nN)) => qb.
  case: (hyp (n -c k) qb qa eq1); [by right | move <-; left ].
  by rewrite double_diff.
move: (NS_le_nat lkn nN) => kN.
case:(cle_eqVlt ll); first by left.
move/(cleSltP kN) => lskh rq1.
move: (cleT lskh (cle_halfn_n nN)) => lskn.
move: (half_monotone2 (NS_succ kN) nN lskh) => /(binom_monotone4 nN lkn) le3.
by case: (proj2(clt_leT le3 (binom_max nN lskn))).
Qed.


Lemma card_partitions_p3 E m p: natp m  -> natp p ->
  cardinal E = m +c p ->
  cardinal (partitions_pi (variantLc m p) E) =
  binom (m +c p) m.
Proof.
  move=> mN pN cE; move: (card_partitions_p2 mN pN cE); simpl.
set x:= cardinal _.
set n := factorial _.
set d := (factorial _)  *c _.
move=> [p1 p2 p3 p4 p5].
have r1: m <=c (m +c p) by apply: csum_M0le; fprops.
have r2:((m +c p) -c m = p) by rewrite csumC; apply: cdiff_pr1; fprops.
rewrite cprodC in p2.
by rewrite (cdivides_pr2 p3 p4 p1 p5 p2) (binom_pr1 (NS_sum mN pN) mN r1) r2. 
Qed.

Lemma card_partitions_p4 E n m: natp n -> natp m ->
  cardinal E = n ->
  cardinal (partitions_pi (variantLc m (n -c m)) E) =
  binom n m.
Proof.
move=> nN mN cE.
case: (NleT_el mN nN) => mn.
  rewrite -(cdiff_pr mn) in cE.
  by rewrite (card_partitions_p3 mN (NS_diff m nN) cE) (cdiff_pr mn). 
rewrite binom_bad // (cdiff_wrong (proj1 mn)).
have cE': cardinal E = n +c \0c by rewrite csum0r; fprops.
set w := partitions_pi _ E; case: (emptyset_dichot w).
  move=> ->; apply: cardinal_set0.
move=> [t] /partitions_piP pip.
have [df cVg [fgf duj ue]] := pip.
have aux:= (pip_prop0 pip).
have ad: inc C0 (domain (variantLc m \0c)) by aww.
move: (cVg _ ad); aw=> eq1.
have tA:inc C0 (domain t) by rewrite df; aww.
by move: (sub_smaller (aux _ tA)); rewrite eq1 cE => /(cltNge mn).
Qed.

Definition subsets_with_p_elements p E:=
  Zo (\Po E)(fun z=> cardinal z = p).

Lemma card_p_subsets n p E: natp n -> natp p ->
  cardinal E = n ->
  cardinal (subsets_with_p_elements p E) = binom n p.
Proof.
move=> nN pN cEn; symmetry.
set src := partitions_pi (variantLc p (n -c p)) E.
set trg:=  subsets_with_p_elements p E.
have cn: cardinalp n by fprops.
have cp: cardinalp p by fprops.
case: (cleT_el cp cn); last first.
  move=> np; rewrite binom_bad//.
  case: (emptyset_dichot trg); first by move=> ->; rewrite cardinal_set0.
  move=> [y] /Zo_P [] /setP_P yE cy.
  by move: (sub_smaller yE); rewrite cEn cy =>/(cltNge np).
move=> pn.
move:(cdiff_pr pn) (NS_diff p nN) => ps sN. 
move: (cEn); rewrite -ps; move=> cEn'.
rewrite -(card_partitions_p3 pN sN cEn') -/src.
clear cEn'; apply /card_eqP.
exists (Lf (Vg ^~C0) src trg); saw.
apply: lf_bijective.
- move=> z /partitions_piP pip.
  have ta: inc C0 (domain z) by move: pip => [p1 _]; rewrite p1; aww.
  apply: Zo_i; first by move: ((pip_prop0 pip) _ ta) => /setP_P.
  move: (proj32 pip); aw =>cp';  rewrite (cp' _ inc_C0_C2); aw; trivial.
- have aux: forall w, inc w src ->  (Vg w C1 = E -s (Vg w C0)).
    move=> w /partitions_piP [df cVg [fgf duj ue]].
    have dgw: (domain w = C2) by rewrite df; aw.
    rewrite /mutually_disjoint dgw in duj.
    case: (duj _ _  inc_C0_C2 inc_C1_C2) => di1; first by case:C1_ne_C0. 
    set_extens u; rewrite - ue. 
      move => h1; apply /setC_P; split. 
         union_tac; rewrite dgw; fprops.
      move=> h2; empty_tac1 u.
    move /setC_P=> [] /setUb_P [y]; rewrite dgw; case /C2_P => -> //.
  move=> u v us vs sWa.
  have sWb: Vg u C1 = Vg v C1 by rewrite  (aux _ us) (aux _ vs) sWa.
  move: us vs => /partitions_piP [df cVg [fgf _ _]]
                 /partitions_piP [df' cV'[fgf' _ _]].  
  apply: fgraph_exten =>//; first by rewrite df'.
  by rewrite df; aw;move=> x; case /C2_P => ->.
- move=> y /Zo_P [] /setP_P yE cyp.
  have aux:partition_w_fam (partition_with_complement E y) E.
    by apply: is_partition_with_complement.
  exists (variantLc y (E -s y)); aw; trivial.
  apply /partitions_piP; saw.
  move=> i itp; try_lvariant itp; trivial.
  rewrite (cardinal_setC4)  ? cEn ? cyp //; apply /NatP; ue.
Qed.


Lemma bijective_complement n p E: natp n -> natp p ->
  p <=c n -> cardinal E = n ->
  bijection (Lf (complement E)
    (subsets_with_p_elements p E)(subsets_with_p_elements (n -c p) E)).
Proof.
move=> nN pN pn cE.
apply: lf_bijective.
- move=> z /Zo_P [] /setP_P ze p1; apply: Zo_i.
    apply /setP_P;apply: sub_setC. 
  rewrite cardinal_setC4 ?cE ?p1 //; apply /NatP; ue.
- move => u v /Zo_P [] /setP_P h1 _ /Zo_P [] /setP_P h2 _. 
  by rewrite -{2}(setC_K h1) -{2}(setC_K h2) => ->.
- move=> y /Zo_P [] /setP_P yE cy;exists (E -s y); last by rewrite (setC_K yE).
  apply: Zo_i; first by apply /setP_P; apply: sub_setC.
  have fse: finite_set E by apply /NatP; ue.
  rewrite (cardinal_setC4 yE fse) cy cE; apply: double_diff => //.
Qed.

Definition graphs_sum_eq F n:=
  Zo (gfunctions F (csucc n)) (fun z => csum z = n).
Definition graphs_sum_le F n:=
  Zo (gfunctions F (csucc n)) (fun z => csum z <=c n).

Lemma graphs_sum_leP F n: natp n -> forall f,
  inc f (graphs_sum_le F n) <->
  [/\ domain f = F, csum f <=c n,  fgraph f & cardinal_fam f].
Proof.
move=> nN f.
split.
   move=> /Zo_P [/gfunctions_P2 [qa qb qc] qd]; split => //.
   by move => i idf; case /(NleP nN): (qc _ (inc_V_range qa idf)).
move =>[qa qb qc qd]; apply: Zo_i => //; apply/gfunctions_P2; split => //.
move => t /(range_gP qc)  [i idf ->]; apply /(NleP nN).
exact: (cleT (csum_increasing6 (qd i idf) idf) qb).
Qed.

Lemma graphs_sum_eqP F n: natp n -> forall f,
  inc f (graphs_sum_eq F n) <->
  [/\ domain f = F, csum f = n, fgraph f & cardinal_fam f].
Proof.
move=> nN f.
split.
   move=> /Zo_P [/gfunctions_P2 [qa qb qc] qd]; split => //.
   by move => i idf; case /(NleP nN): (qc _ (inc_V_range qa idf)).
move =>[qa qb qc qd]; apply: Zo_i => //; apply/gfunctions_P2; split => //.
move => t /(range_gP qc)  [i idf ->]; apply /(NleP nN).
rewrite - qb; exact: (csum_increasing6 (qd i idf) idf).
Qed.

Lemma sum_of_gen_binom E F n: natp n -> cardinal E = n ->
  csumb  (graphs_sum_eq F n) (fun p => cardinal (partitions_pi p E))
  = (cardinal F) ^c n.
Proof.
move=> cE cEn.
rewrite - {2}cEn cpowcr cpowcl. 
pose g f i:=  (Vfi1 f i).
pose f1 f := (Lg F (fun i=> cardinal (g f i))).
pose f2 f := Lg F (g f).
have p1: forall f, inc f (functions E F) ->
     (inc (f1 f) (graphs_sum_eq F n) /\ inc (f2 f) (partitions_pi (f1 f) E)).
  move=> f /functionsP [ff sf tf].
  have sfa: (source f = unionb (Lg (target f) (g f))).
    set_extens t.
      move => tsf; apply /setUb_P; aw.
      have Wt := (Vf_target ff tsf).
      ex_tac; rewrite LgV//; apply /iim_fun_set1_i => //.
    move => /setUb_P; aw; move => [y ytg]; rewrite LgV// => h.
    by case /(iim_fun_set1_P _ ff): h.
  have md: mutually_disjoint (Lg (target f) (g f)).
    apply: mutually_disjoint_prop2 => i j y itf jtf pa pb.
    by rewrite (iim_fun_set1_hi ff pa) (iim_fun_set1_hi ff pb).
  split; last first.
    rewrite /f1 /f2;apply /partitions_piP; hnf; saw.
       move => i iF; rewrite !LgV//.
     hnf; rewrite -tf;split;fprops; ue.
  rewrite /f1; apply /(graphs_sum_eqP _ cE);aw; rewrite /cardinal_fam /allf.
  split; [exact | rewrite - cEn - sf sfa | fprops |].
    apply: Eqc_disjointU => //.
      rewrite /disjointU_fam; hnf;aw; split;fprops.
      move=> i itf; rewrite !LgV//; aw; trivial;ue.
    apply: mutually_disjoint_prop2; aw => i j y pa pb; aw.
      rewrite !LgV //.
      by move /indexed_P => [_ _ <-] /indexed_P  [_ _ <-].
  aw =>  i iF; rewrite LgV//; fprops.
set G:= Lg (graphs_sum_eq F n) 
    (fun p => (Zo (functions E F) (fun f=> f1 f = p))).
have g1: unionb G = (functions E F).
  rewrite /G; set_extens f.
    by move /setUb_P ;aw; move => [y ys]; rewrite LgV//; move /Zo_P => [].
  move => fsf ;move: (p1 _ fsf) => [fa fb]; apply /setUb_P; aw.
  by ex_tac;rewrite LgV//; apply: Zo_i.
have g2: mutually_disjoint G.
  by apply: mutually_disjoint_prop2 => i j y ip jp /Zo_hi <- /Zo_hi <-.
symmetry;  rewrite /cpow -g1.
apply: Eqc_disjointU; fprops; rewrite /G/disjointU_fam; saw.
move=> p pd; rewrite !LgV//; aw.
apply/card_eqP.
set X:= Zo _ _.
exists (Lf f2 X (partitions_pi p E)); saw.
apply: lf_bijective.  
    by move=> t /Zo_P [ts <-]; move: (p1 _ ts) => [].
  move=> u v /Zo_P [] /functionsP [fu su tu] f1u 
             /Zo_P [] /functionsP [fv sv tv] f1v Weq.
  apply: function_exten =>//; try ue.
  move=> x xsu /=.
  have WF: inc (Vf u x) F by Wtac.
  move: (f_equal (Vg ^~(Vf u x)) Weq); rewrite /f2 /g !LgV// => ieq.
  have : (inc x (Vfi1 u (Vf u x))).
     by  apply: iim_fun_set1_i.
  by rewrite ieq; move /(iim_fun_set1_hi fv).
move=> y /partitions_piP ys.
have pip0 := (pip_prop0 ys).
have [df cVg [fgf duj ue]] := ys.
have doi: domain p = F by move /(graphs_sum_eqP _ cE): pd => [].
rewrite doi in cVg. 
pose xf x := select (fun j => inc x (Vg y j)) F.
have xfp: forall x, inc x E -> inc x (Vg y (xf x)) /\ (inc (xf x) F).
  move => x xE;apply: select_pr.
    by move: xE;rewrite -ue => /setUb_P; rewrite df doi.
  rewrite - doi - df. move => a b /= aF va bF vb; case:(duj a b aF bF) => //.
  move => di;empty_tac1 x.
have ta: lf_axiom xf E F by move=> t tE; case:(xfp _ tE).
set x:= Lf xf E F.
have fx: function x by apply: lf_function.
have xsf: inc x (functions E F) by apply /functionsP; rewrite /x;hnf;aw. 
have xp1: forall t, inc t F -> g x t = Vg y t.
  move=> t tF; set_extens u.
    move /(iim_fun_set1_P _ fx) => []; rewrite lf_source => uE.
    rewrite /x LfV //  => -> ; apply : (proj1 (xfp _  uE)).
  move=> uW.
  have usx: inc u (source x). 
    by rewrite -doi - df in tF; rewrite /x; aw; apply: (pip0 _ tF).
  apply:(iim_fun_set1_i fx usx).
  move: usx; rewrite /x lf_source => uE; rewrite LfV//.
  have [tv vF]:= (xfp _ uE).
  move: duj; rewrite /mutually_disjoint;aw; rewrite df doi.
  move=> aux; case: (aux _ _ tF vF) => // d. empty_tac1 u.
have xp2: Lg F (g x) = y.
  symmetry; apply: fgraph_exten =>//; aww; rewrite df //.
  by rewrite doi; move => u uF /=; rewrite LgV////; rewrite - xp1 //.
exists x=>//; apply: Zo_i =>//.
move: pd => /(graphs_sum_eqP _ cE)  [ pa pb pc pd].
apply: fgraph_exten; rewrite /f1; aww. 
move => a aF /=; rewrite !LgV//. rewrite xp1 // cVg //.
Qed.

Lemma sum_of_gen_binom0 E n a:
  natp n ->  cardinal E = n -> finite_int_fam a ->
  (csum a) ^c n = 
     csumb (graphs_sum_eq (domain a) n)
       (fun p =>         
         (cardinal (partitions_pi p E)) *c
            (cprodb (domain a) (fun i=> ((Vg a i) ^c (Vg p i))))).
Proof.
move=> nN cEn fifa.
set F:=csum a; set I := domain a.
have sN:= (finite_sum_finite fifa).
have cF: csum a = cardinal F by symmetry; apply: card_nat.
have [pF] := (card_partitions1 fifa cF).
move /partitions_piP => pipF.
rewrite - {1} cEn cpowcr.
pose g f i := (Vfi f (Vg pF i)).
pose f1 f :=  (Lg I (fun i=> cardinal (g f i))).
pose f2 f := Lg I (g f).
have g_propP: forall f i, inc f (functions E F) -> inc i I ->
    forall x , inc x (g f i) <-> (inc x E /\ inc (Vf f x) (Vg pF i)).
  move=> f i /functionsP [ff sf tf] iI x; rewrite - sf; split.
    rewrite /g; aw; move /iim_fun_P => [u pa pb].
    split; [ Wtac | rewrite - (Vf_pr ff pb) //].
  move => [pa pb]; apply /iim_fun_P; ex_tac; apply: Vf_pr3 =>//.
have prop0F:= (pip_prop0 pipF).
have [da cVa [fga duja uea]] := pipF.
have sfa: forall f, inc f (functions E F) -> unionb (Lg I (g f)) = E.
  move=> f fs; move: (fs) => /functionsP [ff sf tf].
  rewrite - sf;set_extens t => ts.
    move /setUb_P: ts; aw; move => [y yI]; rewrite LgV//.
    by move /(g_propP _ _ fs yI) => []; rewrite sf.
  move: (Vf_target ff ts).
  rewrite tf -uea; move /setUb_P; rewrite da; move=> [y yda Vy].
  apply /setUb_P;exists y => //;aw; trivial;rewrite LgV//; apply/ (g_propP _ _ fs yda).
  split=>//; ue.
have sfb: forall f, inc f (functions E F) ->
      mutually_disjoint (Lg I (g f)).
  move=> f fs;apply: mutually_disjoint_prop2.
  move=> i j y iI jI / (g_propP _ _ fs iI) [yE W1]/(g_propP _ _ fs jI) [_ W2].
  rewrite /I - da in iI jI; case: (duja i j iI jI) => // W; empty_tac1 (Vf f y).
have sfc:forall f, inc f (functions E F) ->
     inc (f2 f) (partitions_pi (f1 f) E).
  move=> f fs; rewrite /f1/f2;apply /partitions_piP; hnf; saw.
    move => i iF; rewrite !LgV//.
  hnf. split; aww.  
have sfd: forall f, inc f (functions E F) -> inc (f1 f) (graphs_sum_eq I n).
  move=> f fs ; apply /(graphs_sum_eqP _ nN); rewrite /f1.
  rewrite - cEn -(sfa _ fs);saw; last first.
  - by  hnf;aw; move =>  i itf; rewrite LgV//; fprops.
  - by fprops.  
  - apply:Eqc_disjointU; fprops.
    split;fprops; rewrite /disjointU_fam; aw; trivial.
    by move => i idf; rewrite !LgV //; aw.
set G:= Lg (graphs_sum_eq I n) 
    (fun p => (Zo (functions E F) (fun f=> f1 f = p))).
have g1: unionb G = (functions E F).
  rewrite /G;set_extens f. 
    by move /setUb_P; aw;move=> [y ys]; rewrite LgV// => /Zo_S.
   move=> fsf;move: (sfd _ fsf) => fa; apply /setUb_P; aw; ex_tac. 
   by rewrite LgV//;apply: Zo_i.
have g2: mutually_disjoint G.
  rewrite /G;apply: mutually_disjoint_prop2.
  by move=> i j y ip jp /Zo_hi <- /Zo_hi <-
.
  rewrite /f1/partitions_pi /partition_with_pi_elements. 
symmetry; rewrite /cpow -g1.
apply: Eqc_disjointU; fprops.
rewrite /disjointU_fam  Lgd.
hnf; aw;split; first by rewrite /G; aw.
move => p pd; rewrite !LgV//.
set X:= (partitions_pi p E).
set Y := productb (Lg I (fun i=> (functions (Vg p i) (Vg pF i)))).
transitivity (cardinal (X\times Y)).
  rewrite - (cardinal_indexed _ p).
  rewrite cprod2_pr1/cprod -/(partitions_pi p E) -/X; aw.
  apply: Eqc_setX; aw; trivial.
  rewrite /cprodb /cprod; aw; apply: Eqc_setXb; hnf ;aw;split;fprops.
  by move=> i iI;rewrite !LgV// double_cardinal -(cVa _ iI) -/(cpow _ _) cpowcl.
set (Z:=  (Zo (functions E F) (fun f => f1 f = p))).
have phi1: forall f, inc f Z -> inc (f2 f) X.
   move=> f /Zo_P [fs f1f];rewrite /X -f1f; apply: sfc =>//.
set WI:= fun f i => equipotent_ex (Vg p i) (g f i).
have W1: forall f i, inc f Z -> inc i I ->
  bijection_prop (WI f i) (Vg p i) (g f i).
  move=> f i fZ iI; rewrite /WI; apply: equipotent_ex_pr1.
  by move: fZ => /Zo_P [fa fb]; rewrite -fb; rewrite /f1 LgV//;aw.
have W2: forall f f' i, inc f Z -> inc f' Z-> inc i I ->
    f2 f = f2 f' -> WI f i = WI f' i.
  move=>  f f' i fZ f'Z iI sf1; rewrite /WI.
  by move: (f_equal (Vg ^~i) sf1); rewrite /f2 !LgV //; move=> ->.
set WJ:= fun f i => (restriction2 f  (g f i) (Vg pF i)) \co  (WI f i).
have W3: forall f i, inc f Z -> inc i I ->
  [/\restriction2_axioms f (g f i) (Vg pF i) ,
   function (restriction2 f  (g f i) (Vg pF i)) &
   (restriction2 f  (g f i) (Vg pF i)) \coP  (WI f i)].
  move=> f i fZ iI.
  have [bVf sVf tW] := (W1 _ _ fZ iI).
  move: fZ=> /Zo_P [feF f1f].
  have g1P := (g_propP _ _ feF iI).
  move: feF => /functionsP [ff sf tf].
  have sgi: sub (g f i) (source f)  by rewrite sf; move=> t /g1P; case.
  have ra:restriction2_axioms f (g f i) (Vg pF i).
    split => //; first by rewrite tf; apply: prop0F; ue.
    by move=> t /(Vf_image_P ff sgi) [u /g1P [uE pr]  ->].
  have fr:= (proj31 (restriction2_prop ra)).
  by split => //; split => //; [ fct_tac | rewrite /restriction2;aw].
set f3:= fun f => (Lg I (WJ f)).
have phi2: forall f, inc f Z -> inc (f3 f) Y. 
  rewrite /f3; move=> f fZ; apply /setXb_P; aw; split;fprops => i iV.
  rewrite !LgV//.
  move: (W3 _ _ fZ iV)(W1 _ _ fZ iV) => [p1 p2 p3][p4 p5 p6].
  rewrite /WJ; apply /functionsP. 
  by saw; [ fct_tac | rewrite /restriction2; aw].
symmetry; apply/card_eqP.
exists (Lf (fun f =>(J (f2 f) (f3 f))) Z (X \times Y)).
hnf;aw;rewrite /G; saw; apply: lf_bijective.
    move=> f fZ; apply:setXp_i; fprops.
  move=> u v uZ vZ eq. 
  move: (pr1_def eq)(pr2_def eq)=> sf2 sf3.
  move: (uZ) => /Zo_S usf.
  move: (uZ)(vZ) => /Zo_P [] /functionsP [fu su tu] f1u 
                    /Zo_P [] /functionsP [fv sv tv] f1v.
  apply: function_exten =>//; try ue.
  rewrite su -(sfa _ usf); move=> x /setUb_P; aw.
  move => [i iI]; rewrite LgV // => xgui.
  move: (f_equal (Vg ^~i) sf3); rewrite /f3 ! LgV// /WJ => eq2.
  move:(W2 _ _ _ uZ vZ iI sf2) => eq3.
  move: (W3 _ _ uZ iI)(W1 _ _ uZ iI) => [p1 p2 p3][p4 p5 p6].
  move: (W3 _ _ vZ iI)(W1 _ _ vZ iI) => [p7 p8 p9][p10 p11 p12].
  rewrite -p6 in xgui.
  move: p4 => [_ sW]; move: ((proj2 sW) _ xgui) => [y ys vy].
  move: (f_equal (Vf ^~ y) eq2); rewrite ! compfV //; last by ue.
  rewrite (restriction2_V p1); last by rewrite - vy -p6.
  rewrite (restriction2_V p7); first by rewrite - eq3 vy.
  Wtac; [ fct_tac |by rewrite p11 -p5 ].
move=> y /setX_P  [py Py Qy].
move: (Py) => /partitions_piP [dy cVy pfay]. 
move: (pfay) =>[fgy dujy uey].
move: (Qy) => /Zo_P; aw; move=> [_ [fgQ dQ Qv]].
move  /(graphs_sum_eqP _  nN): (pd) =>  [fgp dp csp cVip].
set WK:= fun i => equipotent_ex (Vg p i) (Vg (P y) i).
have W4: forall i, inc i I ->
  (bijection_prop (WK i) (Vg p i) (Vg (P y) i)).
  move=> i iI; apply: equipotent_ex_pr1; rewrite - cVy; aw; trivial; ue.
pose hb  i :=  (canonical_injection (Vg pF i) F) \co
  ((Vg (Q y) i) \co (inverse_fun (WK i))).
have Hv:forall i, inc i I ->
  [/\ (Vg (Q y) i) \coP (inverse_fun (WK i)),
   function ( (Vg (Q y) i) \co (inverse_fun (WK i)))
   &  (canonical_injection (Vg pF i) F) \coP
  ((Vg (Q y) i) \co (inverse_fun (WK i)))].
  move=> i iI.
  move: (W4 _ iI)(Qv _ iI); rewrite LgV //; move => [bVf sw tW]. 
  move /functionsP => [fVg sVg tV].
  have p1: (Vg (Q y)i ) \coP (inverse_fun (WK i)).
    split => //; [ by apply: bijective_inv_f | aw; ue].
  have p2:function ((Vg (Q y) i) \co (inverse_fun (WK i))) by fct_tac.
  split => //;split => //. 
    apply: ci_f; apply: prop0F; ue.
  by rewrite /canonical_injection; aw.
have Hw:forall i, inc i I -> function_prop (hb i) (Vg (P y) i) F. 
  move=> i iI.
  move: (Hv _ iI) => [p1 p2 p3];rewrite /hb.
    hnf;rewrite compf_s compf_s compf_t.
  split; first (by fct_tac); last by rewrite /canonical_injection; aw.
  rewrite  ifun_s; by move: (W4 _ iI); move => [bVf sw tW].
rewrite -fgp -dy in Hw.
move: (extension_partition1 pfay Hw). 
set w := common_ext _ _ _;move => [[fw sw tw] alaw].
rewrite dy fgp in alaw.
have wsf:inc w (functions E F) by apply /functionsP.
have gp1: forall j x, inc j I -> inc x (Vg (P y) j) ->
    inc (Vf w x) (Vg pF j).
  move=> j x jI xV.
  move: (alaw _ jI) =>[p1 p2 p3]; rewrite (p3 _ xV).
  move: (Hv _ jI) => [p4 p5 p6].
  move: (W4 _ jI) (Qv _ jI);rewrite LgV //; move => [awj sWj tWj].
  move /functionsP => [fVj sVj tVj].
  rewrite /hb; set aux := (Vg (Q y) j) \co  _. 
  have xsa: inc x (source aux) by rewrite /aux; aw; rewrite tWj.
  have xta: inc (Vf aux x) (Vg pF j).
       have <-:(target aux = Vg pF j) by rewrite /aux; aw.
       Wtac.
    rewrite compfV//  ci_V //; apply: prop0F; ue.
have gp2: forall i, inc i I -> g w i = Vg (P y) i.
  move => i iI; set_extens x. 
     move /(g_propP _ _ wsf iI) => []; rewrite - uey; move /setUb_P.
     move=> [j]; rewrite dy fgp => jI xVj pa.
     have Wp':= (gp1 _ _ jI xVj).
     hnf in duja; rewrite da in duja; case: (duja _ _ iI jI) => h; try ue.
     empty_tac1 (Vf w x).
  move: (alaw _ iI)=> [p1 p2 p3] p4; apply /(g_propP _ _ wsf iI). 
  split; [ by rewrite - sw; apply: p1 |  by apply: gp1].
have wZ:inc w Z.
  apply: Zo_i => //.
  apply: fgraph_exten =>//;rewrite /f1; aww; try ue.
  move=> x xI /=; rewrite LgV //; rewrite gp2 //; apply: cVy; ue.
ex_tac.
have ->: (f2 w = P y).
  apply: fgraph_exten =>//;rewrite /f2; aww; try ue.
  move=> x xI /=; rewrite LgV //gp2 =>//.
suff: (f3 w = Q y) by move=> ->; aw.
apply: fgraph_exten =>//;rewrite /f3; aww; try ue.
move => i iI; rewrite LgV//.
move: (W4 _ iI)(Qv _ iI); rewrite LgV//; move =>  [bVf sVf tW].
move => /functionsP [fVg sVg tV]. 
have ww: (WI w i = WK i) by rewrite /WI /WK gp2 //.
move: (W3 _ _ wZ iI); rewrite /WJ ww (gp2 _ iI); move  => [ra rd cr].
apply: function_exten; [apply: compf_f =>//; aw; ue | exact fVg | aw; ue | | ].
  aw; rewrite /restriction2; aw; ue.
rewrite corresp_s => x xs.
have fW: function  (WK i) by fct_tac.
have p1:inc (Vf (WK i)x ) (target (WK i)) by Wtac.
move: (p1); rewrite tW => p11.
rewrite compfV //restriction2_V //.
move: (proj33 (alaw _ iI)); rewrite -tW => p3;rewrite (p3 _ p1) /hb.
have p2: (Vg (Q y) i) \coP (inverse_fun (WK i)).
  split => //; [ by apply: bijective_inv_f | aw; ue].
have p0:function ((Vg (Q y) i) \co (inverse_fun (WK i))) by fct_tac.
rewrite da in prop0F; move: (@prop0F i iI)=> pf0.
have p4:  (canonical_injection (Vg pF i) F) \coP
        ( (Vg (Q y) i) \co (inverse_fun (WK i))).
  by split;fprops;rewrite /canonical_injection; aw.
rewrite !compfV//;aw; trivial.
have <-: x = Vf (inverse_fun (WK i)) (Vf (WK i) x) by rewrite inverse_V2 =>//.
by rewrite ci_V // -tV //; Wtac; rewrite sVg - sVf.
Qed.

Lemma sum_of_gen_binom2 n: natp n ->
  csumb (csucc n) (binom n) = \2c ^c n.
Proof.
move=> nN; symmetry.
have cnn:=(card_nat nN).
rewrite -(cardinal_set2 C0_ne_C1) -/C2 - (sum_of_gen_binom C2 nN cnn).
set f:= fun m => (variantLc m (n -c m)).
rewrite(@csum_Cn2 _ _ (csucc n) f).
  apply: csumb_exten  => x xi;aw. 
  by rewrite (card_partitions_p4 nN (NS_inc_nat (NS_succ nN) xi) cnn).
split => //.
+ move=> m /(NleP nN) mn; move: (cdiff_pr mn) => e1.
  rewrite /f;apply /(graphs_sum_eqP _  nN);split => //;aww.
  hnf; aw => i itp; try_lvariant itp; [ exact:proj31 mn | fprops ].
+ rewrite /f;move=> u v ui vi s; move: (f_equal (Vg ^~C0) s); aw; trivial.
+ move=> y / (graphs_sum_eqP _ nN) [dy sy fgy alc].
  rewrite /cardinal_fam /allf dy in alc.
  move: (alc _ inc_C0_C2) (alc _ inc_C1_C2) => ca cb.
  have abn:  (Vg y C0) +c (Vg y C1) = n.  
    by  rewrite - csum2_pr0 - sy - csum_gr dy.
  move: (nN); rewrite -abn => nN'.
  move: (NS_in_suml ca nN')(NS_in_sumr cb nN') => aN bN.
  move: (csum_M0le (Vg y C1) ca); rewrite abn => an.
  exists (Vg y C0); first by apply /NleP. 
  rewrite /f;apply: fgraph_exten; aww.
  rewrite dy;move=> x xtp; try_lvariant xtp; trivial.
  rewrite -abn csumC cdiff_pr1 //.
Qed.

Lemma sum_of_binomial n: natp n ->
  csumb (csucc n) (binom n) = \2c ^c n.
Proof. 
move=> nN.
rewrite - card_setP.
set (X:= Lg (csucc n) (fun p=>subsets_with_p_elements p n)). 
set (Y:= disjointU_fam X). 
have fgX: fgraph X by rewrite/ X; fprops.
have fgY: fgraph Y by rewrite /Y/disjointU_fam; fprops.
have dx: domain X = domain Y by rewrite /Y/disjointU_fam; aw.
have eqv: forall i, inc i (domain X) -> (Vg X i) =c (Vg Y i).
  by move=> i idX; rewrite /Y/disjointU_fam LgV//; aw.
have mdX: mutually_disjoint X.
   apply: mutually_disjoint_prop2. 
   move=> i j y id jd;rewrite / subsets_with_p_elements.
   by move=> /Zo_hi yi /Zo_hi yj; rewrite -yi -yj.
have mdY: mutually_disjoint Y by rewrite /Y;  fprops.
have <-:unionb X = \Po n. 
  rewrite /X; set_extens t. 
     by move /setUb_P; aw; move=> [y ydx]; rewrite LgV//; move /Zo_P => [].
  move => tp; apply /setUb_P; aw.
  have cxi: (inc (cardinal t)  (csucc n)). 
     apply /(NleP  nN); move: (tp) => /setP_P /sub_smaller.
     by rewrite (card_nat nN).
  by ex_tac; rewrite LgV//; apply: Zo_i.
rewrite (Eqc_disjointU (conj dx eqv) mdX mdY).
apply: csum_pr3; fprops; rewrite /X;aw; trivial => i ix; rewrite !LgV//.
move: (NS_inc_nat (NS_succ nN) ix) => iN.
rewrite (card_p_subsets nN iN (card_nat nN)). 
exact: (card_nat (NS_binom nN iN)).
Qed.

Lemma sum_of_binomial2 a b n:
  natp n ->
  csumb (csucc n) (fun p => (binom n p) *c (a ^c p) *c (b ^c (n -c p)))
  = (a +c b) ^c n.
Proof.
move: n; apply: Nat_induction.
  rewrite succ_zero csumb1 binom00  cdiff_nn ! cpowx0.
  by rewrite !(cprod1r CS1) (card_card CS1).
move=> n nN.
have snN:= (NS_succ nN). 
rewrite {1} /csumb; set fn := Lg _ _ => hrec.
set X:=((a +c b) ^c n).
pose I := csucc n.  
have IN:sub I Nat by apply: NS_inc_nat.
pose q0 i := (a ^c i) *c (b ^c (n -c i)).
pose q1 i := (a ^c (csucc i)) *c  (b ^c ((csucc n) -c (csucc i))).
pose f1 i := (binom n (csucc i)) *c (q1 i).
pose f2 i := (binom n i) *c (q1 i).
pose g1 i := (binom n i) *c  (a ^c i) *c  (b ^c ((csucc n) -c i)).
have P1: csumb I f2 = a *c X.
  pose g i:= a *c  (binom n i) *c (q0 i); rewrite /csumb.
  have ->: Lg I f2 = Lg I g.
    apply: Lg_exten.
    move=> x xi; rewrite /f2 /g (cprodC a _) - cprodA.
    congr (_ *c _); rewrite cprodC /q1 /q0 (cdiff_pr6 nN (IN _ xi)).
    by rewrite (cpow_succ _ (IN _ xi))- !cprodA (cprodC a).
  rewrite /X -hrec /fn cprod2Dn; apply: csumb_exten.
  move=> x xI /=; aw; rewrite cprodA  cprodA  - cprodA //.
have P2: csum (Lg I g1) =  b *c X.
  set (g:= fun i=> b *c ((binom n i) *c (q0 i))).
  have ->: Lg I g1 = Lg I g.
    apply: Lg_exten.
    move=> x /(NleP nN) xi; rewrite /g1/g  (cprodC b _).  
    rewrite - cprodA - cprodA - cprodA.
    by rewrite (cdiffSn nN xi) (cpow_succ _ (NS_diff x nN)).
  rewrite /X -hrec /fn cprod2Dn;apply: csumb_exten.  
  by move=> x xI /=; aw; rewrite - (cprodA (binom n x)). 
rewrite (fct_sum_rec1 _ snN).
have a1: cardinalp (b ^c (csucc n)) by fprops. 
rewrite (binomSn0 nN) cpowx0 (cdiff_n0 snN) (cprod1l CS1) (cprod1l a1).
set ffn:= fun i => _.
have <-: (g1 \0c) = (b ^c  (csucc n)).
   rewrite /g1 cpowx0 (cdiff_n0 snN) (binom0 nN). 
   by rewrite (cprod1l CS1)(cprod1l (CS_pow b (csucc n))).
have <-:csumb I (fun i =>  (f1 i) +c (f2 i)) = (csumb I ffn).
  apply: csumb_exten => i iI. 
  by rewrite /ffn -/(q1 i) /f1 /f2 (binomSnSm nN (IN _ iI)) - cprodA  cprodDl.
rewrite -/(csumb _ _) -(sum_of_sums f1 f2 I) P1 (csumC _ (a *c  X)) - csumA.
have <-: csumb (csucc n) (fun i=> g1 (csucc i)) = (csumb I f1).
apply: csumb_exten=> u uI; rewrite /f1 /g1 - cprodA //.
rewrite -(fct_sum_rec1 g1 snN).
have ->: csumb (csucc (csucc n)) g1 = b *c X.
  have aux:= (cltS nN).
  rewrite (csum_fs _ snN) {2}/g1 (binom_bad nN snN aux).
  rewrite 2! cprod0l csum0r //; apply: CS_csum.
rewrite - cprodDl cprodC (Nsucc_rw nN) cpow_sum2 cpowx1; fprops.
Qed.  

(* Number of increasing functions *)

Definition functions_incr r r' :=
  (Zo (functions (substrate r) (substrate r'))
    (fun z => increasing_fun z r r')).
Definition functions_sincr r r' :=
  (Zo (functions (substrate r) (substrate r'))
    (fun z => strict_increasing_fun z r r')).

Definition functions_incr_nat p n :=
  functions_incr (Nint_co p) (Nint_co n).  
Definition functions_sincr_nat p n :=
  functions_sincr (Nint_co p) (Nint_co n).  


Lemma functions_incr_inv r1 r2 r3 r4:
   r1 \Is r3 -> r2 \Is r4 ->
   (functions_incr r1 r2) =c (functions_incr r3 r4).
Proof.
move => [f isf] [g isg].
have isif:= (inverse_order_is isf).
have isig:= (inverse_order_is isg).
pose Phi h := (g \co h) \co inverse_fun f.
move: (order_isomorphism_increasing isif) => ifsi.
move: (order_isomorphism_increasing isg) => gsi.
move: (order_isomorphism_increasing isf) => fsi.
move: (order_isomorphism_increasing isig) => igsi.
move: (proj43 isf) => [bf sf tf].
move: (proj43 isg) => [bg sg tg].
have fg: function g by fct_tac.
set S := (functions_incr r1 r2); set T := (functions_incr r3 r4).
have ax: lf_axiom Phi S T.
   rewrite /Phi => t; move/Zo_hi => qa.
   move: (increasing_compose3 ifsi qa gsi) =>[qb _ qc].
   by apply: Zo_i => //; move: qb; aw; rewrite tf tg.
apply/card_eqP; exists (Lf Phi S T); saw; apply: lf_bijective => //.
  move => u v /Zo_S /functionsP [fu su tu] /Zo_S /functionsP [fv sv tv].
  move: (proj31 (proj43 isif)) => qa.
  have co3: g \coP u by split => //; ue.
  have co4: g \coP v by split => //; ue.
  have co1: (g \co u) \coP inverse_fun f. 
     split => //; try fct_tac; aw; ue.
  have co2: (g \co v) \coP inverse_fun f. 
     split => //; try fct_tac; aw; ue.
  by move/ (compf_regl qa co1 co2); move/ (compf_regr  bg co3 co4).
move => k /Zo_P [/functionsP [fk sk tk] mk].
move: (increasing_compose3 fsi mk igsi) =>[rb _ rc].
exists  ((inverse_fun g \co k) \co f).
  by apply:Zo_i => //; apply/functionsP; exact: (proj43 rc).
have ma: k \coP f by  move: (proj31 (proj43 fsi)) =>ff; split => //; ue.
have mb: inverse_fun g \coP k by split=>//; aw; try ue; apply: bijective_inv_f.
have mc:  function (k \co f) by fct_tac.
have md:  target g = target (k \co f) by aw; ue.
rewrite /Phi - (compfA mb ma) (compf_lK' bg mc md) (compf_rK) //.
Qed.

Lemma functions_sincr_inv r1 r2 r3 r4:
   r1 \Is r3 -> r2 \Is r4 ->
   (functions_sincr r1 r2) =c (functions_sincr r3 r4).
Proof.
move => [f isf] [g isg].
have isif:= (inverse_order_is isf).
have isig:= (inverse_order_is isg).
pose Phi h := (g \co h) \co inverse_fun f.
move: (order_isomorphism_increasing isif) => ifsi.
move: (order_isomorphism_increasing isg) => gsi.
move: (order_isomorphism_increasing isf) => fsi.
move: (order_isomorphism_increasing isig) => igsi.
move: (proj43 isf) => [bf sf tf].
move: (proj43 isg) => [bg sg tg].
have fg: function g by fct_tac.
set S := (functions_sincr r1 r2); set T := (functions_sincr r3 r4).
have ax: lf_axiom Phi S T.
   rewrite /Phi => t; move/Zo_hi => qa.
   move: (strict_increasing_compose3 ifsi qa gsi) =>[qb _ qc].
   by apply: Zo_i => //; move: qb; aw; rewrite tf tg.
apply/card_eqP; exists (Lf Phi S T); saw; apply: lf_bijective => //.
  move => u v /Zo_S /functionsP [fu su tu] /Zo_S /functionsP [fv sv tv].
  move: (proj31 (proj43 isif)) => qa.
  have co3: g \coP u by split => //; ue.
  have co4: g \coP v by split => //; ue.
  have co1: (g \co u) \coP inverse_fun f. 
     split => //; try fct_tac; aw; ue.
  have co2: (g \co v) \coP inverse_fun f. 
     split => //; try fct_tac; aw; ue.
  by move/ (compf_regl qa co1 co2); move/ (compf_regr  bg co3 co4).
move => k /Zo_P [/functionsP [fk sk tk] mk].
move: (strict_increasing_compose3 fsi mk igsi) =>[rb _ rc].
exists  ((inverse_fun g \co k) \co f).
  by apply:Zo_i => //; apply/functionsP; exact: (proj43 rc).
have ma: k \coP f by  move: (proj31 (proj43 fsi)) =>ff; split => //; ue.
have mb: inverse_fun g \coP k by saw; try ue; apply: bijective_inv_f.
have mc:  function (k \co f) by fct_tac.
have md:  target g = target (k \co f) by aw; ue.
rewrite /Phi - (compfA mb ma) (compf_lK' bg mc md) (compf_rK) //.
Qed.

Lemma functions_incr_nat_prop r r':
   total_order r -> total_order r' ->  
   finite_set (substrate r)  ->  finite_set (substrate r')  -> 
   functions_incr r r'
   =c functions_incr_nat (cardinal (substrate r)) (cardinal (substrate r')).
Proof.
move => ha hb hc hd.
have is1 :=(finite_ordered_interval2 ha hc).
have is2 := (finite_ordered_interval2 hb hd).
by rewrite (functions_incr_inv is1 is2).
Qed.

Lemma functions_sincr_nat_prop r r':
   total_order r -> total_order r' ->  
   finite_set (substrate r)  ->  finite_set (substrate r')  -> 
   functions_sincr r r'
   =c functions_sincr_nat (cardinal (substrate r)) (cardinal (substrate r')).
Proof.
move => ha hb hc hd.
have is1 :=(finite_ordered_interval2 ha hc).
have is2 := (finite_ordered_interval2 hb hd).
by rewrite (functions_sincr_inv is1 is2).
Qed.


Lemma increasing_nat_prop p n:
  natp p -> natp n -> 
  forall f, 
  (inc f (functions_incr_nat p n)  <->
   inc f (functions p n) /\
   forall i j, i <=c j -> j <c p -> Vf f i <=c Vf f j).
Proof. 
move => pN nN f.
move:(proj2 (Nintco_wor p)) (proj2 (Nintco_wor n)).
rewrite (NintE pN)(NintE nN)=> sr1 sr2.
split.
  move => /Zo_P []; rewrite sr1 sr2 => ha hb; split => // i j lij lin.
  have la: gle (Nint_co p) i j.
    by apply /(Nintco_gleP pN).
  by move: hb  => [_ _ _  fp]; move: (fp i j la) =>/(Nintco_gleP nN)/proj1 .
move =>[qa qb]; apply/Zo_P; rewrite sr1 sr2; split => //.
split => //.
- exact:(proj1 (proj1(Nintco_wor p))).
- exact:(proj1 (proj1(Nintco_wor n))).
- by rewrite sr1 sr2; apply/functionsP.
- move => i j /(Nintco_gleP pN) [lij ljp].
  move:(qb _ _ lij ljp) => le1.
  apply/(Nintco_gleP nN); split => //; apply /(NltP nN).
  by move/functionsP: qa =>[ff sf <-]; Wtac; rewrite sf; apply /(NltP pN).
Qed.

Lemma sincreasing_nat_prop p n:
  natp p -> natp n -> 
  forall f, 
  (inc f (functions_sincr_nat p n)  <->
   inc f (functions p n) /\
   forall i j, i <c j -> j <c p -> Vf f i <c Vf f j).
Proof. 
move => pN nN f.
move:(proj2 (Nintco_wor p)) (proj2 (Nintco_wor n)).
rewrite (NintE pN)(NintE nN)=> sr1 sr2.
split.
  move => /Zo_P []; rewrite sr1 sr2 => ha hb; split => // i j [lij nij] lin.
  have la: glt (Nint_co p) i j.
    by split => //; apply /(Nintco_gleP pN).
  by move: hb  => [_ _ _  fp]; move: (fp i j la) =>[/(Nintco_gleP nN)/proj1 ].
move =>[qa qb]; apply/Zo_P; rewrite sr1 sr2; split => //.
split => //.
- exact:(proj1 (proj1(Nintco_wor p))).
- exact:(proj1 (proj1(Nintco_wor n))).
- by rewrite sr1 sr2; apply/functionsP.
- move => i j [/(Nintco_gleP pN) [lij ljp] nij].
  move:(qb _ _ (conj lij nij) ljp) => [le1 ne1]; split => //.
  apply/(Nintco_gleP nN); split => //; apply /(NltP nN).
  by move/functionsP: qa =>[ff sf <-]; Wtac; rewrite sf; apply /(NltP pN).
Qed.

            
Lemma card_sincreasing_nat p n:
  natp p -> natp n -> 
  cardinal (functions_sincr_nat p n) =  binom n p.
Proof. 
move=> pN nN.
suff: bijection (Lf Imf
  (functions_sincr_nat p n) (subsets_with_p_elements p n)).
  move/card_bijection; aw; move ->.
  have nn: cardinal n = n by rewrite (card_card (CS_nat  nN)).
  exact: (card_p_subsets nN pN nn).
set src:= (functions_sincr_nat p n).
set trg:= subsets_with_p_elements _ _.
have ra f: inc f src -> injection f. 
  move => /(sincreasing_nat_prop pN nN) [/functionsP[ff sf tf] fm].
  split => //; rewrite sf => u v /(NltP pN) up /(NltP pN) vp sv.
  case: (cleT_ell (proj31_1 up)(proj31_1 vp)) => h.
  - done.
  - by case: (proj2(fm _ _ h vp)).  
  - by case: (proj2(fm _ _ h up)).  
have ta: lf_axiom Imf  src trg. 
  move=> z  zp.
  apply /Zo_P; rewrite (cardinal_range (ra _ zp)).
  move/(sincreasing_nat_prop pN nN): zp => [/functionsP[ff sf tf] _].
  rewrite sf (card_card (CS_nat pN)) - tf; split => //; apply/setP_P.
  by apply: Imf_Starget.
apply: lf_bijective =>//.
  move=> u v /(sincreasing_nat_prop pN nN) [/functionsP [fu su tu] um].
  move => /(sincreasing_nat_prop pN nN) [/functionsP [fv sv tv] vm] si.
  apply: function_exten => //; try ue.
  rewrite su; move=> x /(NltP pN) xsu; ex_middle Wx.
  pose pr t := t <c p /\ Vf u t <> Vf v t.
  have prx: pr x  by [].
  have xN: natp x.  apply: (NS_lt_nat xsu pN).
  move: (least_int_prop xN prx); set y := least_ordinal _ _. 
  move => [yN [yp ne] yl].
  have ysu: inc y (source u) by  rewrite su; apply/(NltP pN).
  have ysv: inc y (source v) by  rewrite sv; apply/(NltP pN).
  have qa : Vf u y <c n by  apply/(NltP nN); Wtac.
  have qb : Vf v y <c n by  apply/(NltP nN); Wtac.
  case: (cleT_ee (proj31_1 qa)(proj31_1 qb)) => cuv.
    have: inc (Vf u y) (Imf v)by  rewrite - si; apply: Imf_i.
    move/(Imf_P fv) =>[z]; rewrite sv => zp eqa.
    have qc : z <c p by  apply/(NltP pN).
    case: (cleT_ell (proj31_1 yp)(proj31_1 qc)) => cyz.
    + by case: ne; rewrite eqa cyz.
    + by move:(vm y z cyz qc); rewrite - eqa => /cltNge; case.
    + move:(proj2 (um z y cyz yp)); rewrite eqa => ba.
      case: (cltNge cyz); exact: (yl z (NS_lt_nat cyz yN) (conj qc ba)).
  have: inc (Vf v y) (Imf u) by  rewrite si; apply: Imf_i.
  move/(Imf_P fu) =>[z]; rewrite su => zp eqa.
  have qc : z <c p by  apply/(NltP pN).
  case: (cleT_ell (proj31_1 yp)(proj31_1 qc)) => cyz.
  +  by case: ne; rewrite eqa cyz.
  + by move:(um y z cyz qc); rewrite - eqa => /cltNge; case.
  + move:(proj2 (vm z y cyz yp)); rewrite eqa => /nesym ba.
    case: (cltNge cyz); exact: (yl z (NS_lt_nat cyz yN) (conj qc ba)).
move => y/Zo_P [/setP_P stn cardy].
move: (Nat_order_wor) =>[or1 sr1].
have y1: sub y (substrate Nat_order) by rewrite sr1 => t /stn;apply: NS_inc_nat.
move: (iorder_sr (proj1 or1) y1) (worder_total (induced_wor or1 y1)).
set r := induced_order _ _ => sr tor.
have fsi: finite_set (substrate r).
  by rewrite sr; apply:(sub_finite_set stn); apply: finite_set_nat.
move:(finite_total_enum tor fsi); set f := the_ordinal_iso _. 
rewrite sr cardy; move =>[_ [bf sf tf] _ hb _].
have ff: function f by fct_tac.
pose g := Lf (Vf f) p n. 
have ax: lf_axiom (Vf f) p n. move => t tp; apply: stn; Wtac.
have fg: function g by apply: lf_function.
have ig: y = Imf g.
  rewrite - tf - (surjective_pr0 (proj2 bf)); set_extens t.
     move/(Imf_P ff) =>[x xsf ->]; apply/ (Imf_P fg); rewrite /g; aw.
     by rewrite sf in xsf; ex_tac; rewrite LfV//.
   move/(Imf_P fg); rewrite/g; aw; move=> [x xn  ->].
   rewrite LfV//; apply: (Imf_i ff); ue.
exists g => //.
apply /(sincreasing_nat_prop pN nN); split.
  rewrite /g; apply/functionsP; saw.
rewrite /g;move => i j lij ljp.
have jp: inc j p by apply/(NltP pN).
have ip: inc i p by apply/(NltP pN); apply: (clt_ltT lij ljp).
rewrite !LfV//.
by move:(hb _ _ lij ljp) => /iorder_gltP [_ _ [/Nat_order_leP [_ _ qc] sc]].
Qed.

Lemma cardinal_set_of_increasing_functions r r': 
  total_order r -> total_order r' ->  
  finite_set (substrate r)  ->  finite_set (substrate r')  -> 
  cardinal (functions_sincr r r')
  = binom (cardinal (substrate r')) (cardinal (substrate r)).
Proof. 
move => ha hb hc hd.
rewrite (functions_sincr_nat_prop ha hb hc hd).
by rewrite card_sincreasing_nat //; apply/card_finite_setP.
Qed.

Lemma increasing_prop1 p f: natp p -> 
  (forall i, i <=c p -> natp (f i)) ->
  (forall n, n <c p -> (f n) <=c (f (csucc n))) ->
  (forall i j, i <=c j -> j <=c p -> (f i) <=c (f j)).
Proof.
move => pN p1 p2 i j lij ljp.
move: (NS_le_nat ljp pN) => jN.
move: j jN lij ljp.
apply: Nat_induction; first by move => /cle0 -> /p1 /CS_nat /cleR.
move => j jN Hrec /cle_eqVlt; case.
  by move => -> /p1 /CS_nat /cleR.
move/(cltSleP jN) => lij ljp.
exact: (cleT (Hrec lij (cleT (cleS jN) ljp)) (p2 _ (clt_leT (cltS jN) ljp))).
Qed.

Section StrictIncreasing1.

Variable (p: Set) (f: fterm).
Hypothesis pN: natp p.
Hypothesis fN: (forall i, i <c p -> natp (f i)). 
Hypothesis fm: (forall i j, i <c j -> j <c p -> (f i) <c (f j)). 


Lemma strict_increasing_prop1:
  (forall i, i <c p -> i <=c (f i)).
Proof.
move=> i lip.
have iN:= NS_lt_nat lip pN.
move: i iN lip; apply: Nat_induction.
  by move=> /fN /CS_nat h;apply: cle0x.
move=> n nN pn aux.
have le2:=(cltS nN).
have le3:=(fm le2 aux).
have le4:= (pn (clt_ltT le2 aux)).
apply /cleSlt0P; [ fprops | fprops | exact:cle_ltT le4 le3].
Qed.

Lemma strict_increasing_prop2:
  (forall i j, i <=c j -> j <c p -> ((f i) -c i) <=c ((f j) -c j)).
Proof. 
case: (equal_or_not p \0c).
  move => -> i j ij jp; case: (clt0 jp).
move=> pnz.
have [qN ps] := (cpred_pr pN pnz).
set q := cpred p.
have fq: finite_c (cpred p) by fprops.
pose g i := (f i) -c i.
have q1: (forall i : Set, i <=c q -> natp (g i)).
  by move=> i ip; apply: NS_diff; apply: fN; rewrite ps;apply/(cltSleP qN).
have q2:forall n, n <c q -> (g n) <=c (g (csucc n)).
  move=> n np.
  have nN:= (NS_lt_nat np qN).
  have hy:=(strict_increasing_prop1).
  have p1: (csucc n) <c p by rewrite ps; apply: cltSS.
  have p2:= (cle_ltT (cleS nN) p1).
  move: (hy _ p1) (hy _ p2)=> qp1 qp2.
  move: (fN p1)(fN p2) => s1 s2.
  apply/(cltSleP (NS_diff(csucc n) s1)); rewrite - (csucc_diff s1 nN qp1).
  apply: (cdiff_pr7 qp2 (fm (cltS nN) p1) s1).
move=> i j ij jp.
apply: (increasing_prop1 qN q1 q2 ij).
by move: jp; rewrite {1} ps; move /(cltSleP qN).
Qed.

Lemma strict_increasing_prop3 n:
  natp n -> (forall i, i <c p -> (f i) <c (n +c p)) ->
  (forall i, i <c p -> ((f i) -c i) <=c n).
Proof. 
move=> nN fb i ip.
case: (equal_or_not p \0c) => h.
  rewrite h in ip;case: (clt0 ip).
have [qN psq] := (cpred_pr pN h).
move:ip; rewrite psq; move /(cltSleP qN)=> iq.
have qp: ((cpred p) <c p) by  rewrite {2} psq; aww.
apply: (@cleT ((f (cpred p)) -c  (cpred p))).  
 exact: (strict_increasing_prop2 iq qp). 
have aa:= (strict_increasing_prop1 qp).
have csp :=(cdiff_pr aa).
move: (fb _ qp); rewrite - {1} csp. 
have sN: natp ((cpred p) +c  n) by fprops.
rewrite {4} psq (csum_nS _ qN) (csumC n) => /(cltSleP sN).
by move/(csum_le2l qN (NS_diff (cpred p) (fN qp)) nN). 
Qed.

End StrictIncreasing1.

Lemma card_increasing_nat n p: 
  natp n -> natp p ->
  cardinal (functions_incr_nat p (csucc n)) = binom (n +c p) p.
Proof. 
move=> nN pN; move: (NS_succ nN) => sN.
set np := n +c p.
have npN: natp np by rewrite /np; fprops.
set Q1:= functions_incr_nat p  (csucc n).
set Q2:= functions_sincr_nat p np.
move: (increasing_nat_prop pN sN); rewrite -/Q1 => HQ1P.
move: (sincreasing_nat_prop pN npN); rewrite -/Q2 => HQ2P.
pose subi f:=  Lf (fun i=> (Vf f i) -c  i) p (csucc n).
have Hi0:forall f, inc f Q2 -> 
   [/\ (forall i, i <c p -> natp (Vf f i)),
    (forall i j, i <c j -> j <c p -> (Vf f i) <c (Vf f j)) &
    (forall i, inc i p -> (i <=c (Vf f i)))]. 
  move=> f /HQ2P [/functionsP [ff sf tf] sif].
  have aux: (forall i, i <c p -> natp (Vf f i)). 
    by move=> i /(NltP pN) ilp; apply:(NS_inc_nat npN);  Wtac. 
  by split => // i /(NltP pN);  apply: strict_increasing_prop1.
have Hi3:forall f, inc f Q2 ->
    lf_axiom (fun i  =>  (Vf f i) -c i) p (csucc n).
  move=> f fQ2; move: (Hi0 _ fQ2) => [p1 p2 p3].
  move: (strict_increasing_prop2 pN p1 p2) => p4.
  have p5: (forall i, i <c p->  (Vf f i) <c (n +c p)).
    move=> i ip.
    move: fQ2 => / HQ2P [ /functionsP [ff sf tf] vf].
    have /(NltP npN) //:  (inc (Vf f i) np).
      by rewrite -tf; Wtac; rewrite sf;apply/ (NltP pN).
  move=> i /(NltP pN) ip; apply /(NleP nN).
  apply:(strict_increasing_prop3 pN p1 p2 nN p5 ip). 
have Hi1:forall f, inc f Q2 -> inc (subi f) (functions p (csucc n)).
   move=> f fQ2;apply /functionsP; rewrite /subi; hnf;saw.
   by apply: lf_function; apply: Hi3.
have Hi2:forall f, inc f Q2 -> inc (subi f) Q1.
  move=> f fQ2; apply/HQ1P.
  split; first by apply: Hi1.
  move: (Hi0 _ fQ2) (Hi3 _ fQ2)  => [p1 p2 p3] ta.
  move => i j lij ljp.
  move/(NltP pN): (ljp) => qa; move/(NltP pN): (cle_ltT lij ljp) => qb.
  by rewrite /subi !LfV //; aw; apply (strict_increasing_prop2 pN p1 p2).
set (G:= Lf subi Q2 Q1).
have Hi4:function G by rewrite / G; apply: lf_function. 
pose addi f := Lf (fun i=> (Vf f i) +c i) p np.
have pa:forall f, inc f (functions p (csucc n)) ->
    lf_axiom (fun i  => (Vf f i) +c i) p np.
  move=> f /functionsP [ff sf tf] t tE1.
  have /(NleP nN) le1: (inc (Vf f t) (csucc n)) by Wtac.
  by move: tE1 =>  /(NltP pN) p1; apply /(NltP npN); apply: csum_Mlelt.
have pa2: (forall f, inc f (functions p (csucc n)) ->
    inc  (addi f) (functions p np)).
  move=> f fE; rewrite /addi; apply /functionsP;hnf;saw.
  by apply: lf_function;  apply: pa.
have pa3: forall f, inc f Q1 -> inc (addi f) Q2.
  move=> f /HQ1P [fe1e2 incf]; move: (pa _ fe1e2) => ax.
  apply /HQ2P; split; first by  apply:pa2.
  move => i j  lij ljp.
  move/(NltP pN): (ljp) => qa; move/(NltP pN): (clt_ltT lij ljp) => qb.
  rewrite/addi !LfV//.
  have aux: natp (Vf f j).
    apply: (NS_inc_nat sN); move /functionsP: fe1e2 => [ff sf tf]; Wtac.
  exact: (csum_Mlelt aux (incf _ _  (proj1 lij) ljp) lij).
set (F:= Lf addi Q1 Q2).
have ff: function F by apply: lf_function.
have cGF: G \coP F by rewrite /G/F; saw.
have cFG: F \coP G by rewrite /G/F; saw.
have c1i: (G \co F = identity (source F)).
  apply: function_exten; aw;trivial; [fct_tac |apply: identity_f | | ].
    by rewrite /G/F; aw.
  move => x xsf /=;rewrite (idV xsf) compfV //.
  rewrite corresp_s in xsf.
  have aQ2: inc (addi x) Q2 by apply: pa3.
  rewrite /F /G ! LfV// /addi/subi.  
  move: (xsf) => /HQ1P [/functionsP [fx sx tx] icx].
  apply: function_exten; aw =>//. 
     apply: lf_function; apply: Hi3; apply: pa3 =>//.
  move: (Hi3 _ aQ2)=> ta2.
  move=> a aE1 /=; rewrite !LfV//.
    apply: cdiff_pr1; last by apply: (NS_inc_nat pN).
    apply: (NS_inc_nat sN);rewrite -tx//; Wtac.
  by apply: pa; apply /functionsP.
have c2i: (F \co G = identity (source G)).
  apply: function_exten; [fct_tac | fprops |  by aw | by rewrite /F/G; aw | ].
  rewrite /G; aw => x xQ2.
  have qQ1: inc (subi x) Q1 by apply: Hi2.
  move: (xQ2) => /HQ2P  [/functionsP [fx sx tx] icx].
  rewrite idV// compfV // ?lf_source // /F ! LfV// /addi/subi.  
  symmetry; apply: function_exten; aw; trivial.
    apply: lf_function; apply: pa; apply: Hi1=> //.  
  have ta3:= (Hi3 _ xQ2).
  have ta2:=(pa _ (Hi1 _ xQ2)).
  rewrite sx => i isx;  rewrite ! LfV // cdiff_rpr //.
  exact: (proj33 (Hi0 _ xQ2) i isx).
move: (bijective_from_compose cGF cFG c1i c2i) => /proj31.
move/card_bijection; rewrite /F; aw => ->.
by rewrite card_sincreasing_nat.
Qed.
 

Lemma cardinal_set_of_increasing_functions4 r r'
   (n := cardinal (substrate r'))
   (p := cardinal (substrate r)):
      total_order r -> total_order r' ->  
      finite_set (substrate r)  ->  finite_set (substrate r')  -> 
      cardinal (functions_incr r r')
      = binom ((n +c p) -c \1c) p.
Proof. 
move=> tor tor' fsr fsr'.
rewrite (functions_incr_nat_prop tor tor' fsr fsr') -/n -/p.
have nN: natp n by move: fsr' => /NatP.
have pN: natp p by move: fsr  => /NatP.
case: (equal_or_not n \0c) => nz; last first.
  move: (cpred_pr nN nz) => [qa qb].
  rewrite qb (card_increasing_nat qa pN).
  rewrite  (csum_Sn _ qa) - (cpred_pr4 (CS_succ _)) cpred_pr2; fprops.
rewrite nz (Nsum0l pN).
case: (equal_or_not p \0c) => pz.
  rewrite pz (cdiff_wrong cle_01) binom00.
  set qq:= (functions_incr_nat \0c \0c).
  move:empty_function_function => /functionsP xx.
  have efq: inc empty_function qq.
    by apply/(increasing_nat_prop NS0 NS0); split => // i j _ /clt0.
  have ->: qq = singleton empty_function.
    apply:(set1_pr efq) =>  z /(increasing_nat_prop NS0 NS0) /proj1.
    by rewrite functions_empty => /set1_eq.
  by  rewrite cardinal_set1.
move: (cpred_pr pN pz) => [ppN sp].
rewrite - (cpred_pr4 (CS_nat pN)) (binom_bad ppN pN (cpred_lt pN pz)).
case: (emptyset_dichot (functions_incr_nat p \0c)).
  by move=> ->; apply: cardinal_set0.
move=> [f /(increasing_nat_prop pN NS0) [/functionsP [ff sf tf]] _].
have : inc (cpred p) (source f). rewrite sf {2} sp; apply /(NleP); fprops.
by move/ (Vf_target ff); rewrite tf => /in_set0.
Qed.





  
(* --- *)

  
Lemma binom_2plus n: natp n ->
  binom (csucc n) \2c =  (n *c (csucc n)) %/c \2c.
Proof. move=> nN;rewrite binom2//.  Qed.

Lemma binom_2plus0 n: natp n ->
  binom (csucc n) \2c = (binom n \2c) +c n.
Proof. 
move=> nN.
by rewrite - succ_one (binomSnSm nN NS1) (binom1 nN).
Qed.

Lemma cardinal_pairs_lt n: natp n ->
  cardinal (Zo (coarse Nat) 
    (fun z => [/\ \1c <=c (P z), (P z) <c (Q z) &  (Q z) <=c n])) =
  (binom n \2c).
Proof. 
move=> nN; rewrite /coarse.
set (E:= Nint1c n).
set T:=Zo _ _.  
move: NS1 NS2 => oN tN.
case: (p_or_not_p (\2c <=c n)); last first.
  case: (cleT_el CS2 (CS_nat nN)). 
    by move=> h h'.
  move=> h _; rewrite binom_bad //. 
  case: (emptyset_dichot T); first by move=> ->; rewrite cardinal_set0.
  move=> [p /Zo_P [a1 [a2 a3 a4]]];move: a3.
  by case: (clt2 (cle_ltT a4 h)) => ->; [move /clt0 | move => /(cleNgt a2) ].
move=> le2n.
have cE: cardinal E = n by rewrite card_Nint1c. 
rewrite - (card_p_subsets nN tN cE). 
apply /card_eqP.
exists (Lf (fun z=> (doubleton (P z) (Q z))) T 
    (subsets_with_p_elements card_two E)).
saw; apply: lf_bijective.
    move=> z /Zo_P [zp [le1p [lepq npq] leqn]]. 
    move: (cleT lepq leqn) (cleT le1p lepq) => a1 a2.
    have pE: inc (P z) E by  apply /Nint_ccP1. 
    have qE: inc (Q z) E by apply /Nint_ccP1.
    apply: Zo_i; last by apply: cardinal_set2.
    by apply /setP_P; apply: sub_set2.
 move=> u v /Zo_P [] /setX_P [pu _ _] [_ lt1 _]
     /Zo_P [] /setX_P [pv _ _] [_ lt2 _] h.
  case: (doubleton_inj h); move=> [e1 e2].
    apply: pair_exten =>//.  
    by move: lt1;rewrite e1 e2; move => [/(cltNge lt2)].
move => y  /Zo_P [] /setP_P yE cy2.
have [a [b [p1 p2 aN bN]]]:  exists a, exists b, 
   [/\ a <c b, doubleton a b = y, natp a & natp b].
  have: sub y Nat by apply: (sub_trans yE); apply: Nint_S.
  move /set_of_card_twoP: cy2 => [a [b [ab ->]]] yN.
  move: (yN _ (set2_1 a b))(yN _ (set2_2 a b)) => aN bN.
  case: (NleT_el aN bN); [  by exists a, b | by rewrite set2_C ;exists b, a].
exists (J a b); aw => //.
apply: Zo_i; aw; first fprops.
have: inc a E by apply: yE; rewrite -p2; fprops.
have: inc b E by apply: yE; rewrite -p2; fprops.
by move /(Nint_ccP1 NS1 nN) => [_ pb] /(Nint_ccP1 NS1 nN) [pc _].
Qed.

Lemma cardinal_pairs_le n: natp n ->
  cardinal(Zo (coarse Nat) 
    (fun z=> [/\ \1c <=c  (P z), (P z) <=c (Q z) & (Q z) <=c n])) =
  (binom (csucc n) \2c).
Proof.
move=> nN.
rewrite (binom_2plus0 nN).
rewrite - cardinal_pairs_lt // /coarse.
set E1 := Zo _ _; set E2 := Zo _ _. 
have s21: sub E2 E1.
  move=> t /Zo_P [pa [pb [pc _] pd]]; apply: Zo_i => //.
rewrite -(cardinal_setC s21). 
suff: (E1 -c E2 = n) by move => ->.
set (T:= Nintcc \1c n). 
have ->: n = cardinal T by rewrite card_Nint1c. 
apply /card_eqP.
exists  (Lf P (E1 -s E2) T); hnf;saw.
have cp: forall x, inc x (E1 -s E2) -> P x = Q x.
  move=> x /setC_P [] /Zo_P [xp [le1 le2 ne]] h.
  ex_middle npq; case: h; apply: Zo_i => //.
apply: lf_bijective.
    move=> x xc; move: (cp _ xc). 
    move: xc => /setC_P [] /Zo_P [xp [le1 le2 le]] ns h.
    apply /(Nint_ccP1 NS1 nN); split => //; ue.
  move => u v uc vc; move: (cp _ vc) (cp _ uc) => h1 h2.
  move:  uc vc => /setC_P  [] /Zo_P [] /setX_P [pu _ _] _ _
       /setC_P  [] /Zo_P [] /setX_P [pv _ _] _ _ sp.
   by apply: pair_exten => //; rewrite - h1 -h2 sp.
move=> y => /(Nint_ccP1 NS1 nN) [l1y lyn].
have yN:= NS_le_nat lyn nN.
exists (J y y); aw => //; apply /setC_P; split.
  apply: Zo_i; [ fprops | aw;split;fprops].
by move /Zo_hi => [_  [_ bad] _]; case: bad; aw.
Qed.

Lemma sum_of_i n: natp n ->
  csumb n id =  binom n \2c.
Proof. 
move: n; apply: Nat_induction.
  by rewrite (binom_bad NS0 NS2 clt_02) csum_trivial0.
move=> n nN hr;rewrite induction_on_sum // hr binom_2plus0 //.
Qed.

Lemma fct_sum_const1 f n m:
  natp n ->  (forall i, i <c n -> f i = m) ->
  csumb n f = n *c m.
Proof.
move=> nN p.
by rewrite cprodC - csum_of_same; apply: csumb_exten => i /(NltP nN) /p.
Qed.


Lemma sum_of_i3 n: natp n ->
  csumb n id = binom n \2c.
Proof. 
move=> nN.
move: clt_02 => lt20.
case: (equal_or_not n \0c) => nz.
  by rewrite nz (binom_bad NS0 NS2 clt_02) csum_trivial0.
move: (cpred_pr nN nz); set p := cpred n; move => [pN nsp].
rewrite nsp  (binom2 pN).
set sn:= csumb n id; set aux:=  (p *c (csucc p)).
suff eq: (sn +c sn = aux).
  move:(NS_prod pN (NS_succ pN)); rewrite - /aux - eq => aN.
  have qN: natp sn by apply: NS_in_sumr aN; rewrite /sn/csumb; fprops.
  by rewrite csum_nn -nsp [RHS] even_half.
rewrite /aux cprodC /sn nsp.
rewrite nsp in nN.
have fim: (forall i,  i <c (csucc p) -> (fun i=> i +c (p -ci)) i = p).
  by move=> i /(cltSleP pN) => ilp; apply: cdiff_pr. 
rewrite - (fct_sum_const1 nN fim).
rewrite - (sum_of_sums (fun i => i) (fun i=> (p -c i)) (csucc p)).
apply: f_equal.
by apply: fct_sum_rev.
Qed.

Lemma sum_of_i2 n: natp n ->
  csumb (Nintcc \1c n) id = (binom (csucc n) \2c).
Proof.
move => nN.
rewrite -(sum_of_i3 (NS_succ nN)) -(NintE (NS_succ nN)) - (Nint_co_cc nN). 
move: (sum_of_i3 (NS_succ nN)).
move: (Nint_pr5 nN) => [<- pb].
rewrite csumA_setU1 // csum0r //  /csumb ; fprops.
Qed.

Lemma sum_of_i2bis n: natp n ->
  csumb (Nintcc \1c n) id = (binom (csucc n) \2c).
Proof.
move => nN.
rewrite - cardinal_pairs_le //.
set (E:= Nintcc \1c n).
set X:=Zo _ _ .
set(f:= Lg E (fun k => Zo X (fun z => Q z = k))).
have p1: X = unionb f. 
  rewrite /f; set_extens x.
    move => xX; move/Zo_P: (xX) => [xs [le1 le2 le3]]; apply /setUb_P; aw.
    have qE:inc (Q x) E by have h:= (cleT le1 le2); apply /(Nint_ccP1 NS1 nN).  
    by ex_tac; rewrite LgV//; apply: Zo_i.
  by move=> /setUb_P; aw; move => [y yE]; rewrite LgV//; move /Zo_P => []. 
have p2: f= disjointU_fam (Lg E (fun i => Nintcc card_one i)).
  rewrite /f /disjointU_fam; aw; apply: Lg_exten.
  move=> x xE; move: (xE)=>  /(Nint_ccP1 NS1 nN) [ox xn].
  have xN:= NS_le_nat xn nN.
  rewrite LgV//; set_extens t.
    move =>  /Zo_P [] /Zo_P [] /setX_P [pt _ qN] [oP pq _] qt.
     apply /indexed_P;split => //; apply /(Nint_ccP1 NS1 xN); split => //; ue.
  move /indexed_P => [pt]  /(Nint_ccP1 NS1 xN) [pa pb] pc.
  apply: Zo_i => //; apply /Zo_P; rewrite pc. 
  split => //; apply /setX_P; rewrite pc.
  split => //;apply:NS_le_nat pb xN.
have ->: X = disjointU (Lg E (fun i => Nintcc \1c i)).
  by rewrite  p1 p2 /disjointU.
apply: Eqc_disjointU1.
split;aww => i iE; rewrite ! LgV//.
have iN:= (Nint_S iE).
rewrite card_Nint1c // card_card; fprops.
Qed.

(** number of monomials *)

Lemma set_of_functions_sum0 f:
  (forall a, natp a -> f \0c a = \1c) ->
  (forall a, natp a -> f a \0c = \1c) ->
  (forall a b, natp a -> natp b -> 
     f (csucc a) (csucc b) = (f (csucc a) b) +c (f a (csucc b))) ->
  forall a b, natp a -> natp b -> f a b = (binom (a +c b) a).
Proof. 
move=> p2 p3 p4.
move=> a b aN bN; move: a aN b bN. 
apply: Nat_induction.
  by move=> b bN; rewrite (p2 _ bN) (Nsum0l bN) binom0. 
move=> n nN fnb b bN.
rewrite (csum_Sn _ nN).
move: b bN; apply: Nat_induction.
  have snN: natp (csucc n) by fprops.
  by rewrite (Nsum0r nN) (binom_nn snN) (p3 _ snN).
move=> c cN fsn.
have sc: natp (csucc c) by fprops.
rewrite (p4 _ _ nN cN)  (fnb _ sc) fsn.
by rewrite - (csum_nS _ cN)  (binomSnSm  (NS_sum nN sc) nN).
Qed.


Lemma set_of_functions_sum1 E x n:
  natp n ->  ~ (inc x E) ->
  (graphs_sum_le E n)  \Eq   (graphs_sum_eq (E +s1 x) n).
Proof.
move=> nN nxE.
set (K:= Nintc n).
set (f:= fun z=> z +s1 (J x (n -c (csum z)))).
exists (Lf f (graphs_sum_le E n) (graphs_sum_eq (E +s1 x) n)).
hnf;saw; apply: lf_bijective.
+ move => z /(graphs_sum_leP _ nN) [dz lez fgz alc].
  apply /(graphs_sum_eqP _ nN).
  have p0: (fgraph (f z)) by  apply: fgraph_setU1 => //; ue.
  have p1: (E +s1 x) = domain (f z) by rewrite -dz domain_setU1 //.
  have xd: inc x (domain (f z)) by rewrite -p1; fprops.
  have Vx2: Vg (f z) x = (n -c (csum z)) by rewrite /f setU1_V_out //; ue.
  have p2: cardinal_fam (f z).
    rewrite -dz in nxE; hnf.
    rewrite -p1; move=> i /setU1_P; case.
      rewrite -dz => idz; rewrite /f setU1_V_in //; apply: alc=>//.
    move => ->; rewrite Vx2; fprops.
  split => //.
  rewrite - (Lg_recovers p0) -p1 -/(csumb _ _) csumA_setU1 // -dz /csumb.
  have ->:  (Lg (domain z) (Vg (f z))) = z.
        apply /fgraph_exten => //;aw; fprops => t tf; rewrite /f LgV //.
        rewrite setU1_V_in => //; ue.
  by rewrite  Vx2; apply:cdiff_pr.
+ move => u v /(graphs_sum_leP _ nN) [fu su tu _].
  move /(graphs_sum_leP _ nN) => [fv sv tv _].
  apply: extension_injective => //; ue.
+ move=> y /(graphs_sum_eqP _ nN) [fy sy ty suy].
  have pa: fgraph (Lg E (Vg y)) by fprops.
  have pb: cardinal_fam (Lg E (Vg y)).
    hnf; aw => t tE; rewrite LgV//; apply: suy; rewrite fy; fprops.
  have pc : n = csum (Lg E (Vg y)) +c  Vg y x.
    rewrite - sy -{1} (Lg_recovers ty) -/(csumb (domain y) _).
    by rewrite fy (csumA_setU1 _ nxE).
  have pd: Vg y x = n -c csum (Lg E (Vg y)).
     rewrite pc in nN; rewrite pc csumC cdiff_pr1 //.
     apply: (NS_in_sumr _ nN); apply: suy; rewrite fy; fprops.
     apply: (NS_in_suml _ nN); fprops.
  exists (Lg E (Vg y)).
  apply /(graphs_sum_leP _ nN); saw; rewrite pc.
    apply:csum_M0le; fprops.
  symmetry; rewrite /f;apply: fgraph_exten; fprops.
  + by  apply fgraph_setU1; fprops; aw.
  + by rewrite domain_setU1; aw.
  + rewrite domain_setU1; aw => t; case /setU1_P => te.
      by rewrite setU1_V_in // ? LgV//; aw.
    by rewrite te setU1_V_out //; aw.
Qed.

Lemma set_of_functions_sum2 E n: natp n -> 
  cardinal(graphs_sum_le E (csucc n))
  = (cardinal (graphs_sum_eq E (csucc n)))
    +c (cardinal (graphs_sum_le E n)).
Proof.
move => nN.
have snN: natp (csucc n) by fprops.
set A:= (graphs_sum_eq E (csucc n)).
set B:= (graphs_sum_le E (csucc n)).
set C:= (graphs_sum_le E n).
have di: disjoint A C.
  apply: disjoint_pr.
  move=> u; move /(graphs_sum_eqP _ snN) => [_ pb _ _].
  move /(graphs_sum_leP _ nN) => [_].
  by rewrite pb => qa; move: (cleNgt qa (cltS nN)). 
suff: B = A \cup C by move => ->; rewrite (csum2_pr5 di) csum2cl csum2cr.
set_extens t.
  move /(graphs_sum_leP _ snN) => [pa pb pc1 pc2]; apply /setU2_P.
  case: (equal_or_not (csum t) (csucc n)) => h.
    left; apply /(graphs_sum_eqP _ snN); split => //.
  right; apply /(graphs_sum_leP _ nN); split => //.
  by apply /(cltSleP nN); split.
case /setU2_P.
   move /(graphs_sum_eqP _ snN) => [pa pb pc1 pc2].
   apply /(graphs_sum_leP _ snN);split => //; rewrite pb; fprops.
move /(graphs_sum_leP _ nN) => [pa pb pc1 pc2].
apply /(graphs_sum_leP _ snN);split => //.
apply:cleT pb (cleS nN).
Qed.


Lemma set_of_functions_sum3 E:
  cardinal (graphs_sum_le E \0c) = \1c.
Proof.
have zb:= NS0.
set w:= graphs_sum_le _ _.
suff ->: (w = singleton (Lg E (fun _ =>\0c))) by apply: cardinal_set1.
apply: set1_pr.
  apply /(graphs_sum_leP _ zb); aw;split; fprops.
    rewrite -/(csumb _  _) csum_of_same cprod0l; fprops. 
  hnf; aw => t ti; rewrite LgV //; fprops.
move => z /Zo_P [/gfunctions_P2 [pa pb pc] _].
rewrite - (Lg_recovers pa) - pb; apply: Lg_exten => i ie/=.
by move: (pc _ (inc_V_range pa ie)); rewrite succ_zero => /set1_P.
Qed.

Lemma set_of_functions_sum4 n: natp n ->
    cardinal (graphs_sum_le emptyset n) = \1c.
Proof. 
move=> nN.
suff: (graphs_sum_le emptyset n =singleton emptyset).
  by move=> ->;apply: cardinal_set1.
apply: set1_pr.
  apply /(graphs_sum_leP _ nN);split; [by aw | | fprops | ].
  + rewrite csum_trivial; aww; exact (cle0n nN).
  + apply: fgraph_set0.
  + by move => t;rewrite domain_set0 => /in_set0.
by move => z/ (graphs_sum_leP _  nN) [ /domain_set0_P g df _ _].
Qed.

Lemma set_of_functions_sum_pr n h
  (intv:= fun h => (Nint h))
  (sle:= fun n h => graphs_sum_le (intv h) n)
  (seq := fun n h =>  graphs_sum_eq (intv h) n)
  (A:= fun n h => cardinal (sle n h))
  (B:=  fun n h => cardinal (seq n h)):
  natp n  -> natp h  ->
  (A n h =  B n (csucc h) /\ A n h = (binom (n +c h) n)).
Proof. 
move=> nN hN.
have AB: forall a  b, natp a -> natp b -> A a b = B a (csucc b).
  move=> a b aN bN; rewrite /A /B /sle/seq; apply /card_eqP.
  move: (Nint_pr4 bN) => [p1 p2].
  rewrite /intv -p1; apply: (set_of_functions_sum1 aN p2). 
split; first by apply: AB.
have Hv: forall a b, natp a -> natp b ->
  A (csucc a) b = (B (csucc a) b) +c (A a b).
  move=> a b aN bN; rewrite /A/B /sle /seq.
  by rewrite - (set_of_functions_sum2  (intv b) aN).
apply: set_of_functions_sum0.
- move=> a aN; rewrite /A/sle; apply:  set_of_functions_sum3.
- move=> a aN;rewrite /A/sle. 
  have ->: (intv \0c = emptyset).
    by rewrite /intv;apply: Nint_co00. 
  apply: set_of_functions_sum4 =>//.
- move=> a b aN bN.
  by rewrite (Hv _ _ aN (NS_succ bN)) -(AB _ _ (NS_succ aN) bN). 
- exact.
- exact.
Qed.


Definition csum_to_increasing_fun y :=
  fun i => csumb (csucc i) (Vg y).

Definition csum_to_increasing_fct y n p :=
  Lf (csum_to_increasing_fun y) (csucc p) (csucc n).

Lemma csum_to_increasing1 y n p:
  natp n -> natp p ->
  inc y (graphs_sum_le (csucc p) n) ->
  lf_axiom (csum_to_increasing_fun y) (csucc p)  (csucc n).
Proof. 
move=> nN pN /(graphs_sum_leP _ nN) [dy dyxx les alc] u /(NleP pN)  up.
apply /(NleP nN); apply: cleT dyxx.
apply: csum_increasing1; rewrite dy; exact: (proj33 (cleSS up)).
Qed. 

Lemma csum_to_increasing2 n p:
  natp n -> natp p ->
  lf_axiom (fun y=> (csum_to_increasing_fct y n p))
  (graphs_sum_le (csucc p) n) 
  (functions_incr_nat (csucc p) (csucc n)).
Proof.
move=> nN pN y ys.
have spN :=  (NS_succ pN); have snN:= (NS_succ nN).
move: (csum_to_increasing1 nN pN ys) => ta1.
rewrite /csum_to_increasing_fct.
have aa: (forall u, inc u (domain y)-> inc (Vg y u) (csucc n)).
  move: ys => /Zo_P [/gfunctions_P2 [pa pb pc ] pd] u udy.
  exact: (pc _ (inc_V_range pa udy)).
move: ys => /(graphs_sum_leP _ nN)  [dy fhy les alc].
set g:= Lf _ _ _ .
have p1: function g by apply: lf_function.
apply/(increasing_nat_prop spN snN); split.
  by apply /functionsP; split => //; rewrite /g;aw.
move => i j leij lejs.
have jsp: inc j (csucc p) by apply /NltP.
have isp: inc i (csucc p) by apply /(NltP spN); apply: (cle_ltT leij lejs).
rewrite /g ! LfV //.
rewrite /csum_to_increasing_fun /csumb -/(restr _ _) -/(restr _ _).
have sab := (proj33 (cleSS leij)).
by rewrite - (double_restr _  sab); apply: (csum_increasing1); aw.
Qed.

Lemma csum_to_increasing4 n p:
  natp n -> natp p ->
  injection (Lf (fun y=>  (csum_to_increasing_fct y n p))
  (graphs_sum_le (csucc p) n) 
  (functions_incr_nat (csucc p) (csucc n))).
Proof.
move=> nN pN; apply: lf_injective; first by apply: csum_to_increasing2.
rewrite /csum_to_increasing_fct.
move=> u v us vs h.
move: (csum_to_increasing1 nN pN vs)=> ta2.
have aux: forall x, inc x (csucc p) ->
    csumb  (csucc x) (Vg u) = csumb (csucc x) (Vg v).
  move=> x xi; move: (f_equal (Vf ^~ x) h); rewrite !LfV//.
  by apply: csum_to_increasing1.
clear h.
move/Zo_S: (us) => /gfunctions_P2 /proj33 ru.
move/Zo_S: (vs) => /gfunctions_P2 /proj33 rv.
move /(graphs_sum_leP _ nN): us=> [du lesu fgu alcu].
move /(graphs_sum_leP _ nN): vs => [dv lesv fgv alcv].
apply: fgraph_exten =>//; first by ue.
move=> x xdu.
move: (ru _ (inc_V_range fgu xdu)) => xu.
rewrite du - dv in xdu; move: (rv _ (inc_V_range fgv xdu)) => xv.
move:(NS_inc_nat (NS_succ nN) xu) (NS_inc_nat (NS_succ nN) xv) => xuN xvN.
rewrite dv in xdu; move: (aux x xdu).
move: (NS_inc_nat (NS_succ pN) xdu) => xN.
rewrite (csum_fs _ xN)(csum_fs _ xN).
case: (equal_or_not x \0c)=> zx.
  by rewrite {1 3} zx ! csumb0 !Nsum0l.
move /(NltP (NS_succ pN)): xdu => /proj1 le0.
have le1: (csumb x (Vg v)) <=c csum v. 
  move: (proj33 le0); rewrite - dv => xdv.
  by apply: csum_increasing1. 
have l1x:= (cge1 (CS_nat xN) zx).
move: (cpred_pr6 pN l1x le0) =>[pa pb pc].
move: (NS_le_nat (cleT le1 lesv) nN) => sb.
suff: csumb x (Vg u)  = csumb x (Vg v) by move ->;  apply: csum_eq2l.
by rewrite pb; apply: aux; apply/(NleP pN).
Qed.


Lemma csum_to_increasing5 n p:
  natp n -> natp p ->
  surjection (Lf (fun y=>  (csum_to_increasing_fct y n p))
  (graphs_sum_le (csucc p) n) 
  (functions_incr_nat (csucc p) (csucc n))).
Proof. 
move=> nN pN; apply: lf_surjective. 
  by apply: csum_to_increasing2.
have spN :=  (NS_succ pN); have snN:= (NS_succ nN).
move =>y /(increasing_nat_prop spN snN) [/functionsP [fy sy ty] qb].
have rec:(forall u, u <> \0c -> inc u (csucc p) ->
    [/\ inc (cpred u) (csucc p), u = csucc (cpred u) &
       (Vf y (cpred u)) <=c (Vf y u)]).
  move=> u unz usy.
  move /(NltP (NS_succ pN)): (usy) => /proj1 le0.
  have uN := NS_inc_nat (NS_succ pN) usy.
  have l1u:= (cge1 (CS_nat uN) unz).
  move: (cpred_pr6 pN l1u le0) =>[pn sp pc].
  have hu: inc (cpred u) (csucc p) by apply/NleP.
  have le1:= (cpred_le (CS_nat uN)).
  by split => //; apply: (qb _ _ le1); apply/NltP.
pose f i := Yo(i= \0c) (Vf y \0c) ((Vf y i) -c  (Vf y (cpred i))).
have f1p: (forall i, inc i (csucc p) -> inc (f i) (csucc n)).
  move=> i i1; rewrite /f; Ytac h; first by rewrite -ty; Wtac; rewrite sy -h.
  move: (rec _  h i1) => [vsy usv  wle].
  rewrite - sy in i1 vsy.
  move:(Vf_target fy i1); rewrite ty ; move /(NleP nN) => win.
  apply /(NleP nN). 
  exact: (cleT (cdiff_ab_le_a (Vf y (cpred i)) (proj31 win)) win).
pose h i := csumb (csucc i) f.
have H x: inc x (csucc n) -> cardinalp x by case/(NleP nN).
have h1: forall i, inc i (csucc p) -> h i = Vf y i.
  move=> i /(NleP pN) ip; move: (NS_le_nat ip pN) => iN.
  rewrite/h/f;move: i iN ip; apply: Nat_induction.
    move => hh; rewrite succ_zero csumb1; Ytac0; rewrite card_card //.
    by apply/H; Wtac; rewrite sy; apply/(NleP pN); apply: cle0n.
  move=> m mN; rewrite /h => hr /(cleSltP mN) lmp.
  have smN: natp (csucc m) by fprops.
  have snz:= (@succ_nz m).
  have smsy: (inc (csucc m) (csucc p)) by  apply/(NleP pN); apply/cleSltP.
  move: (rec _ snz smsy) => [vsy vp]. 
  rewrite (csum_fs _ smN) /f (Y_false snz) (hr (proj1 lmp)).
  rewrite (cpred_pr1 (CS_nat mN)); apply: cdiff_pr.
have p1: inc (Lg (csucc p) f) (graphs_sum_le (csucc p) n).
  apply /(graphs_sum_leP _ nN); split; aww.
    have pp:= (Nsucc_i pN).
    rewrite [csum _] (h1 _ pp); apply/(NleP nN); Wtac.
   hnf;aw. move => x xp; rewrite LgV//; exact: (H _ (f1p x xp)).
rewrite/csum_to_increasing_fct; ex_tac.
move :(csum_to_increasing1 nN pN p1) => aux.
apply: function_exten; aw;trivial; first by apply: lf_function.
rewrite sy; move=> x xsy /=; rewrite LfV// -(h1 _ xsy).
apply: csumb_exten => t ts; rewrite LgV //; apply/(NleP pN). 
move/(NleP pN): xsy => l1; move/(NleP (NS_le_nat l1 pN)): ts => l2.
apply:(cleT l2 l1).
Qed.

Lemma csum_to_increasing6 n p:
  natp p -> natp n ->
  cardinal (graphs_sum_le (csucc p) n) =
  binom (csucc (n +c p)) (csucc p).
Proof. 
move=> pN nN.
rewrite - (csum_nS _ pN).
rewrite - (card_increasing_nat nN (NS_succ pN)).  
apply /card_eqP.
exists (Lf (fun y=> (csum_to_increasing_fct y n p))
    (graphs_sum_le (csucc p) n) 
    (functions_incr_nat (csucc p) (csucc n))).
hnf;saw. 
by split; [apply: csum_to_increasing4 | apply: csum_to_increasing5].  
Qed.


Lemma nat_to_B_fact n: nat_to_B (n`!) = factorial (nat_to_B n).
Proof.
elim: n; first by rewrite factorial0 fact0 - succ_zero //.
move=> n Hr; rewrite factS nat_to_B_prod Hr - nat_to_B_succ cprodC.
rewrite factorial_succ //; apply: nat_to_B_Nat.
Qed.

Lemma nat_to_B_binom m n: 
   nat_to_B 'C(m,n) = binom (nat_to_B m) (nat_to_B n).
Proof.
have H:=  nat_to_B_Nat.
move:m n; elim.
  case => //; first by  rewrite binom0 -? succ_zero //; fprops.
  by move => m; rewrite bin0n /= binom0Sm.
move => n Hr [| m]. 
    rewrite bin0 binom0 - ? succ_zero //; apply: nat_to_B_Nat.
rewrite binS nat_to_B_sum Hr Hr - !nat_to_B_succ - binomSnSm //. 
Qed.


Lemma nat_to_B_quorem a b :
  nat_to_B(a %/ b) = (nat_to_B a) %/c (nat_to_B b) /\
  nat_to_B(a %% b) = (nat_to_B a) %%c (nat_to_B b).
Proof.
case: (posnP b) => bp.
  by rewrite bp  divn0 modn0 /= (crem_zero (nat_to_B_Nat a)) cquo_zero.
move: (f_equal nat_to_B (divn_eq a b)).
rewrite mulnC nat_to_B_sum nat_to_B_prod => h.
apply: cquorem_pr;try apply:nat_to_B_Nat.
by split => //; apply/nat_to_B_lt; apply:ltn_pmod.
Qed.


End IntegerProps.
Export IntegerProps.

