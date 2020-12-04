(** * Theory of Sets EIII-4  Natural integers. Finite sets
  Copyright INRIA (2009-2018) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: sset8.v,v 1.6 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.

Require Export sset7.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Module CardinalOps.

(** ** EIII-3-3 Operations on Cardinals *)
Definition csum x := cardinal (disjointU x).
Definition cprod x := cardinal (productb x).
Definition csumb a (f: fterm) := csum (Lg a f).
Definition cprodb a (f: fterm) := cprod (Lg a f).

Lemma csum_pr0 I f : csumb I f = csumb I (fun i => cardinal (f i)).
Proof.
by apply: Eqc_disjointU1;split;aww => i idx; rewrite !LgV //; aw.
Qed.
 
Lemma cprod_pr0 I f : cprodb I f = cprodb I (fun i => cardinal (f i)).
Proof.
by apply: Eqc_setXb; split; aww => i idx; rewrite !LgV //; aw.
Qed.

Lemma csum_gr f: csumb (domain f) (Vg f) = csum f. 
Proof.
congr cardinal; rewrite /disjointU /disjointU_fam; aw.
by congr unionb; apply:Lg_exten => x xdf; rewrite !LgV.
Qed.

Lemma cprod_gr f: cprodb (domain f) (Vg f) = cprod f.
Proof. congr cardinal;apply: @productb_gr. Qed.

Lemma csumb_exten A f g : {inc A, f =1 g} -> csumb A f = csumb A g.
Proof. by move=> h; congr csum; apply: Lg_exten. Qed.

Lemma cprodb_exten A f g : {inc A, f =1 g} -> cprodb A f = cprodb A g.
Proof. by move => h; congr cprod; apply: Lg_exten. Qed.

Lemma CS_csum f: cardinalp (csum f).
Proof. rewrite /csum; fprops. Qed.

Lemma CS_cprod f: cardinalp (cprod f).
Proof. rewrite /cprod; fprops. Qed.

Global Hint Resolve  CS_csum CS_cprod: fprops.

Theorem cprod_pr f: cprod f = cprodb (domain f) (fun a => cardinal (Vg f a)).
Proof. by rewrite - cprod_gr; apply cprod_pr0. Qed.

Theorem csum_pr f:  csum f = csumb (domain f) (fun a => cardinal (Vg f a)).
Proof. rewrite - csum_gr; apply: csum_pr0. Qed.


Lemma csum_pr3 f g:
  domain f = domain g ->
  (forall i, inc i (domain f) -> Vg f i =c Vg g i) ->
  csum f = csum g.
Proof. by move=> dfg sc; rewrite 2!csum_pr -dfg; apply:csumb_exten. Qed.

Lemma csum_pr4 f: 
   mutually_disjoint f -> 
   cardinal (unionb f) = csumb (domain f) (fun a => cardinal (Vg f a)).
Proof.
move => pa; rewrite - csum_pr.
apply: Eqc_disjointU => //; last exact (@disjointU_disjoint f).
by rewrite /disjointU_fam; saw => i idx; rewrite LgV // Eq_indexed_c.
Qed.

Lemma csum_pr4_bis X f: 
  (forall i j, inc i X -> inc j X -> i = j \/ disjoint (f i) (f j)) ->
  cardinal (unionf X f) = csumb X (fun a => cardinal (f a)).
Proof.
move => mdx1.
have mdx: mutually_disjoint (Lg X f).
  by hnf; aw => i j iX jX; rewrite !LgV //; apply:mdx1.
by rewrite setU_bf (csum_pr4 mdx); aw; apply:csumb_exten => t tx; rewrite LgV.
Qed.

Lemma csum_pr1 f:
  cardinal (unionb f) <=c csumb (domain f) (fun a => cardinal (Vg f a)).
Proof. 
rewrite -(csum_pr f);apply: surjective_cle. 
move: (disjointU_pr f) => /=; set g := common_ext _ _ _.
by move => [sf tg srfj _]; exists g.
Qed.

Lemma csum_pr1_bis X f:
  cardinal (unionf X f) <=c csumb X (fun a => cardinal (f a)).
Proof. 
rewrite setU_bf; move:(csum_pr1 (Lg X f));congr (_ <=c _).
by aw; apply:csumb_exten => t tx; rewrite LgV.
Qed.

Theorem csum_Cn X f: 
  target f = domain X -> bijection f -> 
  csum X = csum (X \cf (graph f)).
Proof. 
move=> tf [[ff injf] sjf].
have sf:source f = domain (graph f) by rewrite domain_fg.
pose X' := Lg (domain X) (Vg X).
pose g:= Lg (source f)  (fun i => (Vg  (X' \cf (graph f)) i) *s1 (Vf f i)).
have ->:  X \cf (graph f) = (Lg (source f) (fun z => Vg X (Vf f z))).
  by rewrite /composef -(proj33 ff); apply: Lg_exten => i idf; rewrite /X';aw.
rewrite -(csum_gr X) /csumb /csum /disjointU/ disjointU_fam Lgd.
set h := Lg _ _.
have fgh: fgraph h by  rewrite/h;fprops.
have imfh: Imf f = domain h by rewrite (surjective_pr0 sjf) /h; aw.
rewrite (setUb_rewrite1 ff fgh imfh).
have aux x : inc x (source f ) -> inc (Vg (graph f) x) (domain X)
  by rewrite - tf; apply: Vf_target. 
have <-: (g = h \cf (graph f)). 
  have sf1: source f = domain (h \cf graph f)by rewrite composef_domain.
  rewrite /g;apply: fgraph_exten; aww => x xsf; move: (aux _ xsf) => aa.
  have xdf: inc x (domain (graph f)) by ue.
  by rewrite !LgV.
apply: Eqc_disjointU.
- rewrite /g; saw => i isf;  move: (aux _ isf) => aa.
  rewrite !LgV //; aw; trivial;ue.
- rewrite /g; apply: mutually_disjoint_prop; aw => i j y isf jsf.
  rewrite !LgV // - ? sf //; try apply: aux => //.
  move /setX_P => [_ _ /set1_P e1] /setX_P [_ _ /set1_P e2].
  rewrite e1 in e2;  apply: (injf _ _ isf jsf e2); ue.
apply:disjointU_disjoint.
Qed.


Theorem cprod_Cn X f:
  target f = domain X ->  bijection f -> 
  cprod X = cprod (X \cf (graph f)). 
Proof.
move=> tF bijf;apply /card_eqP.
exists (product_compose X f); hnf;rewrite lf_source lf_target.
split => //; [by apply: pc_fb | rewrite /composef domain_fg //; fct_tac].
Qed.
  
Theorem csum_An f g:
  partition_w_fam g (domain f) ->
  csum f = csumb (domain g) (fun l => csumb (Vg g l) (Vg f)).
Proof. 
move=> pfg; rewrite/csumb/csum; set h := fun l:Set => _.
rewrite/disjointU/disjointU_fam Lgd.
set g0 := fun i:Set => _.
transitivity (cardinal (unionb (Lg (domain g) (fun l => unionf (Vg g l) g0)))).
  f_equal;rewrite /unionb; aw;rewrite - (proj33 pfg) setUf_A.
  apply: setUf_exten; move => t tdf; rewrite LgV//.
  apply: setUf_exten; move=> i idg; rewrite LgV//; union_tac.
apply: Eqc_disjointU;fprops; aw; last first.
- by apply: mutually_disjoint_prop3. 
- apply: mutually_disjoint_prop2; rewrite /g0=> u v  y udg vdg; aw. 
  move /setUf_P => [u' u'Vg /setX_P [py Py /set1_P Qy]].
  move /setUf_P => [v' v'Vg /setX_P [py' Py' /set1_P Qy']].
  case :(proj32 pfg  _ _ udg vdg) =>// di.
  rewrite -Qy' Qy in v'Vg; case: (nondisjoint u'Vg v'Vg di).
split; aww => i idg; rewrite !LgV//.
rewrite setU_bf /h /disjointU/disjointU_fam /g0;  aw; trivial.
apply: Eqc_disjointU; try apply:mutually_disjoint_prop3. 
by split; aww; move=> j jVg; rewrite !LgV.  
Qed.

Theorem cprod_An f g:
  partition_w_fam g (domain f) ->
  cprod f = cprodb (domain g) (fun l => cprodb (Vg g l) (Vg f)).
Proof.
move=> pfa. 
transitivity (cprodb (domain g) (fun l => restriction_product f (Vg g l))).
  apply/card_eqP.
  by exists (prod_assoc_map f g); split; first (by apply: pam_fb);
    rewrite/ prod_assoc_map; aw.
apply: Eqc_setXb => //; split; aww. 
by move=> i idg; rewrite /cprodb /cprod /restriction_product !LgV //; aw.
Qed.


Theorem cprodDn f:
  cprodb (domain f) (fun l => csum (Vg f l)) =
  csumb (productf (domain f) (fun l => (domain (Vg f l))))
    (fun g => (cprodb (domain f) (fun l => Vg (Vg f l) (Vg g l)))).
Proof. 
transitivity (cprodb (domain f) (fun l => disjointU (Vg f l))).
  by apply: Eqc_setXb;split; aww => i idf; rewrite /csum !LgV //; aw.
set (g:= Lg (domain f) (fun l => disjointU_fam (Vg f l))).
transitivity(cprodb (domain g) (fun l => unionb (Vg g l))).
  rewrite/cprodb /cprod /g;  f_equal; f_equal.
  aw; apply: Lg_exten; move=> x xdg; rewrite LgV//.
rewrite/cprodb/cprod -/(productf _ _) distrib_prod_union //.
have dg: domain g = domain f by rewrite /g;  aw.
set ld:= productf _ _.
have lde: ld = productf (domain f) (fun l => domain (Vg f l)).
  rewrite /ld/productf dg; apply: f_equal; apply: Lg_exten.
  by move=> x xdg; rewrite /g  LgV // Lgd.
rewrite setU_bf - lde.
apply: Eqc_disjointU;last by fprops.
  saw; first by rewrite/ disjointU_fam; aw. 
  move=> i ip; rewrite !LgV //; aw; trivial.
  set h :=  (productb (Lg (domain f) (fun l  => Vg (Vg f l) (Vg i l)))).
  apply: Eqc_setXb; split => //; aww.
  move=> k kdg; rewrite /g /disjointU_fam -dg; aw; rewrite !LgV //; aw; trivial.
  move: ip; rewrite lde; move/setXf_P => [_ dif]; apply; ue.
have myel: forall i j y, inc i ld
    -> inc y (productf (domain f) (fun l => Vg (Vg g l) (Vg i l))) ->
  inc j (domain f) ->  Q (Vg y j) = Vg i j. 
  rewrite /g/ disjointU_fam lde. 
  move=>k j y; aw=> /setXf_P [fgk dk kp1] /setXf_P [fgy dy yp1] jdf.
  move: (kp1 _ jdf)=> iVjk.
  by move: (yp1 _ jdf); rewrite !LgV //; move /setX_P => [_ _ /set1_P].
apply: mutually_disjoint_prop; aw.
move=>i j y ild jld; rewrite dg !LgV // => xp yp.
apply: (setXf_exten ild jld) => k kdf /=; rewrite dg in kdf.
by rewrite - (myel _ _ _ ild xp kdf) - (myel _ _ _ jld yp kdf).
Qed.

Definition quasi_bij (f: fterm) I J := 
  [/\ (forall x, inc x I -> inc (f x) J),
  (forall x y, inc x I -> inc y I -> f x = f y -> x = y) &
  (forall y, inc y J -> exists2 x, inc x I &  y = f x)].

 
Fact quasi_bij_prop f I J g (F := (Lf f I J)) (G := Lg J g) :
  quasi_bij f I J ->
  [/\ target F = domain G, bijection F &
    G \cf (graph F) = Lg I (fun z => Vg G (f z))].
Proof.
move=> [p1 p2 p3].
rewrite /F /G; saw;  first by apply: lf_bijective.
rewrite /Lf corresp_g /composef Lgd; apply: Lg_exten => i ij. 
by rewrite (LgV ij).
Qed.

Lemma csum_Cn2 J g I f : quasi_bij f I J ->
  csumb J g = csumb I (fun z => (g (f z))).
Proof.
move=> h; move:(quasi_bij_prop g h) => [tF bF vF].
rewrite /csumb (csum_Cn tF bF) vF; apply:csumb_exten.
by move => i  iI /=; rewrite LgV//; apply: (proj31 h).
Qed.

Lemma cprod_Cn2 J g I f : quasi_bij f I J ->
  cprodb J g = cprodb I (fun z => (g (f z))).
Proof.
move=> h; move:(quasi_bij_prop g h) => [tF bF vF].
rewrite /cprodb (cprod_Cn tF bF) vF; apply:cprodb_exten.
by move => i iI; rewrite LgV//; apply: (proj31 h).
Qed.

Fact csum_prod_assoc_aux I J (f: fterm2):
  csumb I (fun i => csumb J (fun j => f i j)) =
  csumb J (fun j => csumb I (fun i => f i j)) /\
  cprodb I (fun i => cprodb J (fun j => f i j)) =
  cprodb J (fun j => cprodb I (fun i => f i j)). 
Proof.
pose h := Lg (I \times J) (fun z => f (P z) (Q z)).
pose g1 := Lg I (fun i => indexedr i J).
pose g2 := Lg J (fun j => indexed I j).
have par2: partition_w_fam g2 (domain h).
   rewrite /g2 /h; split.
   - fprops.
   - apply: mutually_disjoint_prop3.
   -  rewrite - setU_bf; aw;set_extens t.
       move=>/setUf_P [j jJ /indexed_P [pa pb pc]].
       apply/setX_P; split => //; ue.
     by move/setX_P => [qa qb qc]; apply/setUf_P; ex_tac; apply/indexed_P.
have par1: partition_w_fam g1 (domain h).
  rewrite /g1 /h; split.
 - fprops.
 - apply: mutually_disjoint_prop2 => u v y _ _.
   by move=> /setX_P [_ /set1_P <- _] /setX_P [_  /set1_P <- _]. 
 - rewrite - setU_bf; aw; set_extens t.
     move=>/setUf_P [j jJ /indexedrP [pa pb pc]].
     apply/setX_P; split => //; ue.
   by move/setX_P => [qa qb qc]; apply/setUf_P; ex_tac; apply/indexedrP.
have qa i: inc i I -> quasi_bij Q (indexedr i J) J.
  move => iI; split.
  - by move => x /setX_P [].  
  - move => x y /indexedrP [pa pb  pc] /indexedrP [pa' pb'  pc'] rq.
    apply: pair_exten => //; ue. 
  - move => y yJ; exists (Pair.J i y); aw; last trivial.
    by apply/indexedrP; split; aww.
have qb j: inc j J -> quasi_bij P (indexed I j) I.
  move => iI; split.
  - by move => x /setX_P [].  
  - move => x y /indexed_P [pa pb  pc] /indexed_P [pa' pb'  pc'] rq.
    apply: pair_exten => //; ue. 
  - move => y yJ; exists (Pair.J y j); aw; last trivial.
    by apply/indexed_P; split;aww.
split.
  move: (csum_An par2); rewrite  (csum_An par1) /g1/g2; aw.
  set A := csumb _ _; set B :=csumb _ _;set C := csumb _ _; set D:= csumb _ _.
  have ->: A = C.
    apply csumb_exten => i iI; rewrite LgV// (csum_Cn2 _ (qa _ iI)).
    apply: csumb_exten => j /indexedrP [sa sb sc]; rewrite/h LgV //; first ue.
    apply/setX_P;  split => //; ue.
  have -> //: B = D.
    apply csumb_exten => i iI; rewrite LgV // (csum_Cn2 _ (qb _ iI)). 
    apply: csumb_exten => j /indexed_P [sa sb sc]; rewrite/h LgV//; first ue.
   apply/setX_P;  split => //; ue.
move: (cprod_An par2); rewrite  (cprod_An par1) /g1/g2; aw.
set A := cprodb _ _; set B :=cprodb _ _;set C := cprodb _ _; set D:= cprodb _ _.
have ->: A = C.
  apply cprodb_exten => i iI; rewrite LgV// (cprod_Cn2 _ (qa _ iI)). 
  apply: cprodb_exten => j /indexedrP [sa sb sc]; rewrite/h LgV//; first ue.
  apply/setX_P;  split => //; ue.
have -> //: B = D.
  apply cprodb_exten => i iI;rewrite LgV// (cprod_Cn2 _ (qb _ iI)). 
  apply: cprodb_exten => j /indexed_P [sa sb sc]; rewrite/h LgV//; first ue.
apply/setX_P;  split => //; ue.
Qed.

Lemma csum_An2 I J (f: fterm2):
  csumb I (fun i => csumb J (fun j => f i j)) =
  csumb J (fun j => csumb I (fun i => f i j)).
Proof. exact: (proj1 (csum_prod_assoc_aux I J f)). Qed.
  
Lemma cprod_An2 I J (f: fterm2):
  cprodb I (fun i => cprodb J (fun j => f i j)) =
  cprodb J (fun j => cprodb I (fun i => f i j)). 
Proof. exact: (proj2 (csum_prod_assoc_aux I J f)). Qed.



(** Product and sums of two cardinals *)

Definition csum2 a b := csum (variantLc a b).
Definition cprod2 a b := cprod (variantLc a b).

Notation "x +c y" := (csum2 x y) (at level 50).
Notation "x *c y" := (cprod2 x y) (at level 40).

Lemma CS_sum2 a b: cardinalp (a +c b).
Proof. rewrite/csum2/csumb; fprops. Qed.

Lemma CS_prod2 a b: cardinalp (a *c b).
Proof. rewrite /cprod2/cprodb; fprops. Qed.

Global Hint Resolve CS_sum2 CS_prod2: fprops.

Lemma csum2_pr a b f: doubleton_fam f a b -> a +c b = csum f.
Proof.
move=> /two_terms_bij [g [bg tg ->]]. apply: (csum_Cn tg bg).
Qed.

Lemma csum2_pr0 f : csumb C2 f = f C0 +c f C1.  
Proof. by rewrite  (csum2_pr (doubleton_fam_canon f)). Qed.

Lemma cprod2_pr a b f: doubleton_fam f a b -> a *c b = cprod f.
Proof. move=> /two_terms_bij [g [bg tg ->]]; apply: (cprod_Cn tg bg). Qed.

Lemma cprod2_pr0 f : cprodb C2 f = f C0 *c f C1.  
Proof. by rewrite  (cprod2_pr (doubleton_fam_canon f)). Qed.


Lemma csumC a b: a +c b = b +c a.
Proof. apply: (csum2_pr (doubleton_fam_rev a b)). Qed.

Lemma cprodC a b: a *c b = b *c a.
Proof. by rewrite (cprod2_pr (doubleton_fam_rev a b)). Qed.

Lemma disjointU2_pr3 a b x y: y <> x -> 
  (a +c b) =c ((a *s1 x) \cup (b *s1 y)).
Proof. 
move=> yx.
rewrite -(disjointU2_rw _ _ yx) double_cardinal.
by apply: csum2_pr; apply: doubleton_fam_variant.
Qed.

Lemma csum2_pr5 a b: disjoint a b -> cardinal (a \cup b) =  a +c b.
Proof. 
rewrite -(card_card (CS_sum2 a b)) (disjointU2_pr3 a b C1_ne_C0).
move => dab; apply: (Eqc_disjointU2 dab);aww.
Qed.

Lemma csum2_pr2 a b a' b':
  a =c a' ->  b =c b' ->   a +c b = a' +c b'.
Proof. 
move=> eaa ebb.
rewrite -(card_card (CS_sum2 a b)) -(card_card (CS_sum2 a' b')).
rewrite (disjointU2_pr3 a b C1_ne_C0)(disjointU2_pr3 a' b' C1_ne_C0).
apply:Eqc_disjointU2; aww.
Qed.


Lemma csum2cl x y: (cardinal x) +c y = x +c y.
Proof. exact: (csum2_pr2 (double_cardinal x) (erefl (cardinal y))). Qed.

Lemma csum2cr x y: x +c (cardinal y) = x +c y.
Proof. exact: (csum2_pr2  (erefl (cardinal x)) (double_cardinal y)). Qed.

Lemma cardinal_setC2 a b: sub a b ->
   cardinal b = a +c  (b -s a).
Proof.
by rewrite - (csum2_pr5 (set_I2Cr b a)) setU2_C; move /setCU_K => ->.
Qed.

Lemma cardinal_setC3 a b: 
  (a -s b) =c (b -s a) -> a =c b.
Proof.
rewrite (cardinal_setC2 (@subsetI2l a b)) (cardinal_setC2 (@subsetI2r a b)).
move: (set_CI2 a b a); rewrite setC_v set0_U2 => ->.
move: (set_CI2 b a b); rewrite setC_v set0_U2 setI2_C => -> h.
by rewrite - csum2cr h csum2cr.
Qed.

Lemma cardinal_setC3_rev: exists a b,  a =c b /\ ~  (a -s b) =c (b -s a).
Proof.
move: omega0_pr => [qa qb _].
exists omega0, (osucc omega0); split; first by apply/card_eqP.
have -> :omega0 -s osucc omega0 = emptyset.
  by apply/set0_P => t /setC_P [to]; case; apply: setU1_r.
have ->: (osucc omega0 -s omega0) = singleton omega0.
   set_extens t; first by case/setC_P;case /setU2_P.
   move => /set1_P ->; apply/setC_P; split; first  fprops.
   apply: (ordinal_irreflexive qa).
rewrite cardinal_set0 cardinal_set1; fprops.
Qed.

Lemma cprod2_pr1 a b: a *c b = cardinal (a \times b).
Proof. 
have bf:= (product2_canon_fb a b).
symmetry;apply/card_eqP.
by exists (product2_canon a b); split => //;rewrite/product2_canon; aw.
Qed.

Lemma cprod2_pr2 a b:  (a \times cardinal b) =c (a \times b).
Proof. by apply: Eqc_setX; aw. Qed.

Lemma cprod2cr x y: x *c (cardinal y) = x *c y.
Proof. by rewrite !cprod2_pr1 cprod2_pr2. Qed.

Lemma cprod2cl x y: (cardinal x) *c y = x *c y.
Proof. by rewrite cprodC cprod2cr cprodC. Qed.


Lemma sum_of_sums f g I:
  (csumb I f) +c (csumb I g) = csumb I (fun i => (f i) +c (g i)).
Proof. 
pose h i j := variant C0 (f i) (g i) j. 
move: (csum_An2 I C2 h). rewrite csum2_pr0.
have ->: csumb I (h^~ C0) = csumb I f.
  by rewrite/h; apply:csumb_exten => i iI; rewrite variant_true1.
have ->: csumb I (h^~ C1) = csumb I g.
  by rewrite/h; apply:csumb_exten => i iI; rewrite variant_false1.
move <-.
by apply:csumb_exten => i iI; rewrite csum2_pr0/h  variant_true1 variant_false1.
Qed.

Lemma prod_of_prods f g I:
  (cprodb I  f) *c (cprodb I g) = cprodb I (fun i =>(f i) *c (g i)).
Proof.
pose h i j := variant C0 (f i) (g i) j. 
move: (cprod_An2 I C2 h). rewrite cprod2_pr0.
have ->: cprodb I (h^~ C0) = cprodb I f.
  by rewrite/h; apply:cprodb_exten => i iI; rewrite variant_true1.
have ->: cprodb I (h^~ C1) = cprodb I g.
  by rewrite/h; apply:cprodb_exten => i iI; rewrite variant_false1.
move <-.
by apply:cprodb_exten=> i iI;rewrite cprod2_pr0/h variant_true1 variant_false1.
Qed.


Lemma cprodA a b c:  a *c (b *c c) = (a *c b) *c c.
Proof. 
rewrite (cprodC (a *c b))  !cprod2_pr1 !cprod2_pr2.
move /card_eqP: (Eq_mulA a b c) => ->.
by rewrite  -!cprod2_pr1 cprodC.
Qed.

Lemma csumA a b c: a +c (b +c c) = (a +c b) +c c.
Proof. 
move: a b c.
have aux: (forall u v w  a b c,  v <> u-> u <> w -> w <> v -> 
  a +c (b +c c) = cardinal ((a *s1 u) \cup  ((b *s1 v) \cup (c  *s1  w)))).
  move=> u v w a b c vu uw wv.
  rewrite - (card_card (CS_sum2 a (b +c c))) (disjointU2_pr3 a (b +c c) vu).
  apply: Eqc_disjointU2; fprops.
    apply: disjoint_pr; move=> z; move/setX_P => [_ _ /set1_P pa]
    /setU2_P [] /setX_P [_ _ /set1_P]; rewrite pa => //; apply:nesym => //.
  aw; exact: (disjointU2_pr3 b c wv).
move: C2_ne_C01 => [/nesym ne3 ne2] a b c.
rewrite - (csumC c (a +c b)).
rewrite(aux _ _ _ a b c C1_ne_C0  ne3 ne2) (aux _ _ _ c a b ne3 ne2 C1_ne_C0 ).
by rewrite setU2_A setU2_C.
Qed.

Lemma csumACA: interchange csum2 csum2.
Proof.
move => s1 s2 r1 r2; rewrite (csumA _ s2 r2) (csumA _ r1 r2). 
by rewrite -(csumA s1) (csumC s2 r1) (csumA s1).
Qed.

Lemma cprodACA: interchange cprod2 cprod2.
Proof.
move => s1 s2 r1 r2; rewrite (cprodA _ s2 r2) (cprodA _ r1 r2). 
by rewrite -(cprodA s1) (cprodC s2 r1) (cprodA s1).
Qed.

Lemma csumCA a b c: a +c (b +c c) = b +c (a+c c).
Proof. by rewrite csumC - csumA (csumC c). Qed.

Lemma cprodDr a b c:
  a *c (b +c c) = (a *c b) +c (a *c c).
Proof. 
have aux: forall a b c,  (a \times (b \times c)) =c  ((a *c b) \times c).
  move=> a' b' c'.
  by rewrite - cprod2_pr1 - cprod2cr -2!cprod2_pr1 cprodA.
rewrite cprod2_pr1 -(card_card(CS_sum2 (a *c b) (a *c c))).
rewrite - cprod2_pr2 (disjointU2_pr3 b c C1_ne_C0).
rewrite cprod2_pr2 set2_UXr.
rewrite (disjointU2_pr3 (a *c b) (a *c c) C1_ne_C0).
apply: Eqc_disjointU2.
- by apply: disjointU2_pr0; apply: disjointU2_pr; fprops.
- by apply: disjointU2_pr; fprops.
- by apply: aux.
- by apply: aux.
Qed.

Lemma cprodDl a b c:
  (b +c c) *c a = (b *c a) +c (c *c a).
Proof.
rewrite cprodC (cprodC b a) (cprodC c a); apply: cprodDr.
Qed.

Lemma cprod2Dn a I f: 
  a *c (csumb I f) = csumb I (fun i => a *c (f i)).
Proof.
rewrite cprod2_pr1 /csum cprod2_pr2 /csumb /csum.
rewrite/disjointU distrib_prod2_sum /disjointU_fam; aw.
apply: Eqc_disjointU => //.
- split => //; aww;move=> i idf; rewrite !LgV //.
  by rewrite - cprod2_pr2 cprod2_pr1; aw; rewrite cprod2_pr2.  
- apply: mutually_disjoint_prop2 => i j y idf jdf; rewrite !LgV//.
  move => /setX_P [_ _ /setX_P [_ _ /set1_P <-]].
  by move  => /setX_P [_ _ /setX_P [_ _ /set1_P <-]].
- apply: mutually_disjoint_prop3. 
Qed. 


(** ** EIII-3-4 Properties of the cardinals 0 and 1 *)

Lemma csum_trivial f: domain f = emptyset -> csum f = \0c.
Proof.
move=> dge; rewrite/csum /disjointU /disjointU_fam dge /Lg funI_set0.
by rewrite setUb_0 cardinal_set0.
Qed.

Lemma csum_trivial0 f: csumb emptyset f = \0c.
Proof. by apply:csum_trivial; aw. Qed.

Lemma csum_trivial1 x f: domain f = singleton x -> csum f = cardinal (Vg f x).
Proof. 
rewrite/csum /disjointU/disjointU_fam => ->.
rewrite /unionb Lgd setUf_1 LgV //; aw; trivial; exact:(set1_1 x).
Qed.

Lemma csum_trivial2 x f: domain f = singleton x -> cardinalp (Vg f x) -> 
  csum f =  Vg f x.
Proof. by move=> df cV; rewrite (csum_trivial1 df) (card_card cV). Qed.

Lemma csum_trivial3 x f: csumb (singleton x) f = cardinal (f x).
Proof. 
rewrite /csumb (csum_trivial1 (Lgd (singleton x) f)) LgV//; fprops.
Qed.

Lemma csum_trivial4 f a:
  csum (restr f (singleton a))  = cardinal (Vg f a).
Proof. 
have <-: Vg (restr f (singleton a)) a = Vg f a by rewrite LgV; fprops.
apply: csum_trivial1; rewrite restr_d //.
Qed.

Lemma cprod_trivial f: domain f = emptyset -> cprod f = \1c. 
Proof. 
by move=> /domain_set0_P ->; rewrite/cprod setXb_0 cardinal_set1.
Qed.

Lemma cprod_trivial0 f: cprodb emptyset f = \1c.
Proof. by apply:cprod_trivial; aw. Qed.

Lemma cprod_trivial1 x f: domain f = singleton x -> cprod f = cardinal (Vg f x).
Proof. 
move=> df; symmetry; apply /card_eqP.
exists (product1_canon (Vg f x) x); split.
- apply: setX1_canon_fb. 
- by rewrite /product1_canon; aw.
- by rewrite/ product1_canon; aw;apply: setX1_pr2.
Qed.

Lemma cprod_trivial2 x f: domain f = singleton x ->
  cardinalp (Vg f x) -> cprod f =  Vg f x.
Proof. 
by move=> df cV; rewrite (cprod_trivial1 df) (card_card cV). 
Qed.

Lemma cprod_trivial3 x f: cprodb (singleton x) f = cardinal (f x).
Proof. 
rewrite /cprodb (cprod_trivial1 (Lgd (singleton x) f)) LgV; fprops.
Qed.

Lemma cprod_trivial4 f a:
  cprod (restr f (singleton a)) = cardinal (Vg f a).
Proof. 
have <-: Vg (restr f (singleton a)) a = Vg f a by rewrite LgV; fprops.
apply: cprod_trivial1; rewrite restr_d //.
Qed.

Lemma csumA_setU2 A B f: disjoint A B ->
  csumb (A \cup B) f = csumb A f +c csumb B f.
Proof.
move => /(partition_setU2 f) dab; rewrite /csumb.
rewrite (csum_An dab) variantLc_d csum2_pr0; aw.
apply: f_equal2; apply: csumb_exten => i ia;rewrite LgV; fprops.
Qed.

Lemma csumA_setU1 A b f: ~ (inc b A) ->
  csumb (A +s1 b) f = csumb A f +c (f b).
Proof.
move => /disjoint_setU1 pa. 
by rewrite -csum2cr (csumA_setU2 _ pa) csum_trivial3.
Qed.

Lemma cprodA_setU2 A B f: disjoint A B ->
  cprodb (A \cup B) f = cprodb A f *c cprodb B f.
Proof.
move => /(partition_setU2 f) dab; rewrite /cprodb.
rewrite (cprod_An dab) variantLc_d cprod2_pr0; aw.
apply: f_equal2; apply: cprodb_exten => i ia;rewrite LgV; fprops.
Qed.

Lemma cprodA_setU1 A b f: ~ (inc b A) ->
  cprodb (A +s1 b) f = cprodb A f *c (f b).
Proof.
move => /disjoint_setU1 pc.
by rewrite - cprod2cr  (cprodA_setU2 _ pc) - cprod_trivial3.
Qed.

Lemma card_partition_induced X f F:
  (forall x, inc x X -> inc (f x) F) ->
  cardinal X = csumb F (fun k => cardinal (Zo X (fun z => f z = k))).
Proof.
move => fim; rewrite - csum_pr0; apply /card_eqP.
rewrite disjointU_E; set S := unionf _ _.
exists (Lf (fun x => J x (f x)) X S); hnf; saw; apply lf_bijective.
    move => x xX; move: (fim _ xX) => ok.
    by apply /setUf_P; aw; ex_tac; aw; apply: indexed_pi; apply /Zo_P.
  move => u v _ _ sv; exact: (pr1_def sv).
move => y /setUf_P; aw; move => [z zf]; aw.
move =>/indexed_P [px /Zo_P [pc pd] pe];ex_tac.
by rewrite  -{1} px  pd pe.
Qed.

Lemma card_partition_induced1 X f F g:
  (forall x, inc x X -> inc (f x) F) ->
  csumb X g = csumb F (fun i => csumb (Zo X (fun z => f z = i)) g).
Proof.
move => fim.
pose h i := (Zo X (fun z => f z = i)). 
have pa: (partition_w_fam (Lg F h) (domain (Lg X g))).
  aw; split; first by fprops.
    rewrite /h; hnf; aw => i j iF jF.
    rewrite !LgV //; mdi_tac eq1 => u /Zo_hi fu.
    by move /Zo_hi => fv; case: eq1; rewrite -fu fv.
  rewrite /h;set_extens t.  
    by move /setUb_P; aw; move => [y yf]; rewrite LgV//; move => /Zo_P [].
  move => tx; apply /setUb_P; aw; move: (fim _ tx) => ft; ex_tac.
  by rewrite LgV//; apply /Zo_P. 
rewrite {1} /csumb (csum_An pa); aw.
apply:csumb_exten => i iF; rewrite /h !LgV//.
apply:csumb_exten => z zi; rewrite LgV //; apply: Zo_S zi.
Qed.

Theorem csum_zero_unit f j:
  sub j (domain f) ->
  (forall i, inc i ((domain f) -s j) -> (Vg f i) = \0c) ->
  csum f = csumb j (Vg f).
Proof.   
move=> jdf acz; rewrite - csum_gr.
congr cardinal; rewrite disjointU_E disjointU_E.
set_extens x; move /setUf_P; aw; move => [y yd]; aw => h; apply/setUf_P; aw.
  case: (inc_or_not y j)=> yj; first by ex_tac; aw.
  have yc: (inc y ((domain f) -s j)) by apply /setC_P.
  move: h; rewrite (acz _ yc)=> /setX_P [_ /in_set0 [] _]. 
by exists y; aw; trivial;apply: jdf.
Qed.

Theorem cprod_one_unit f j:
  sub j (domain f) ->
  (forall i, inc i ((domain f) -s j) -> (Vg f i) = \1c) ->
  cprod f = cprodb j (Vg f).
Proof. 
move=> jdf alo; apply /card_eqP; exists (pr_j f j).
by apply: (prj_fb jdf) => i /alo ->; exists emptyset.
Qed.

Lemma csum_zero_unit_bis f:
  (allf f (fun z => z = \0c)) <-> csum f = \0c.
Proof.
split.
  move => ha.
  have hc:(forall i, inc i (domain f -s emptyset) -> Vg f i = \0c).
    by move => i /setC_P [/ha ].
  by rewrite (csum_zero_unit  (sub0_set _) hc) csum_trivial0.
move/card_nonempty; rewrite/disjointU /disjointU_fam => ue.
move => i idf /=;case: (emptyset_dichot (Vg f i)) => // - [x xs].
empty_tac1 (J x i); apply/setUb_P; exists i; aw; trivial.
by rewrite LgV//; apply: indexed_pi.
Qed.

Lemma csum_0l a: \0c +c a = cardinal a.
Proof. by  rewrite - (csum2_pr5 (set0_I2 a)) set0_U2. Qed.
  
Lemma csum0l a: cardinalp a -> \0c +c a = a.
Proof.  by move=> /card_card {2} <-; exact: csum_0l. Qed.

Lemma csum0r a: cardinalp a ->  a +c \0c = a.
Proof. by move => ca;rewrite  csumC csum0l. Qed.

Lemma csum_nz a b: a +c b = \0c -> (a = \0c /\ b = \0c).
Proof. 
move/csum_zero_unit_bis; rewrite/allf; aw => h.
by move:(h _ inc_C0_C2)(h _ inc_C1_C2); aw.
Qed.

Lemma cprod_1r a: a *c \1c = cardinal a.
Proof. by  rewrite cprod2_pr1 cardinal_indexed. Qed.

Lemma cprod_1l a: \1c *c a = cardinal a.
Proof. by  rewrite cprodC cprod_1r. Qed.

Lemma cprod1r a: cardinalp a ->  a *c \1c = a.
Proof. by move=> ca; rewrite cprod_1r (card_card ca). Qed.

Lemma cprod1l a: cardinalp a ->  \1c *c a = a.
Proof. by move=> ca; rewrite cprodC cprod1r. Qed.

Lemma cprod0r a: a *c \0c = \0c.
Proof. rewrite cprod2_pr1; aw; apply: cardinal_set0. Qed.

Lemma cprod0l a: \0c *c a = \0c.
Proof. by rewrite cprodC cprod0r. Qed.

Lemma cprod_eq0 f:
  (exists2 i, inc i (domain f) & cardinal (Vg f i) = \0c) ->
  cprod f = \0c.
Proof.
move=> [i idf cVz]; rewrite /cprod.
case: (emptyset_dichot (productb f)); first by move => ->; apply: cardinal_set0.
by move /setXb_ne2 => h; move: (h i idf)=> /card_nonempty1.
Qed.

Lemma csum_of_same a b: csumb b (fun i: Set => a) = a *c b.
Proof.
rewrite cprod2_pr1; congr cardinal; rewrite disjointU_E ;set_extens t.
  move=> /setUf_P [y yj]; aw.
  move => /indexed_P [pa pb pc]; apply /setX_P;split => //; ue.
by move /setX_P => [pa pb pc]; apply/setUf_P; ex_tac; aw; apply/indexed_P.
Qed.

Lemma csum_of_ones b: csumb b (fun i: Set => \1c) = cardinal b.
Proof. by rewrite csum_of_same cprod_1l. Qed.

Lemma csucc_pr3 x: csucc (cardinal x) = x +c \1c.
Proof.
move:(ordinal_irreflexive (OS_cardinal (CS_cardinal x))) => w.
rewrite - (double_cardinal x) - (csucc_pr w).
by rewrite(csum2_pr5(disjoint_setU1 w)) - csum2cr csum2cl cardinal_set1.
Qed.

Lemma csucc_pr4 x: cardinalp x -> csucc x = x +c \1c.
Proof. by rewrite - csucc_pr3;move /card_card => ->. Qed.

Lemma csucc_pr5 a: cardinal (csucc a) = csucc a.
Proof. apply: (card_card (CS_succ a)). Qed. 

Lemma csum_11: \1c +c \1c = \2c.
Proof. by rewrite - (csucc_pr4 CS1) succ_one. Qed.

Lemma csum_nn n:  n +c n = \2c *c n.
Proof. by rewrite -csum_11 cprodDl cprod_1l csum2cr csum2cl. Qed.

Definition card_nz_fam f := allf f (fun z => z <> \0c).

Theorem cprod_nzP f: card_nz_fam f <-> (cprod f <> \0c).
Proof. 
split => h. 
  have alne: (forall i, inc i (domain f) -> nonempty (Vg f i)). 
    move=> i /h vz;case: (emptyset_dichot (Vg f i))=> // p.
  move: (setXb_ne alne); apply: card_nonempty1.
move=> i idf /=; dneg vz; apply: cprod_eq0=>//; ex_tac.
by rewrite vz; apply: cardinal_set0. 
Qed.

Lemma cprod2_nz a b: a <> \0c  -> b <> \0c ->  a *c b <> \0c.
Proof. 
by move=> az bz; apply /cprod_nzP; hnf; aw => i itp;try_lvariant itp.
Qed.

Lemma cprod2_eq0 a b: a *c b = \0c -> a = \0c \/ b = \0c.
Proof.
move =>h. 
case: (equal_or_not a \0c) => az; first by left.
case: (equal_or_not b \0c) => bz; first by right.
by case: (cprod2_nz az bz).
Qed.

Theorem succ_injective a b: cardinalp a ->  cardinalp b -> 
  a +c \1c = b +c \1c -> a = b.
Proof. 
move=> ca cb; rewrite - (csucc_pr4 ca)- (csucc_pr4 cb).
by apply: csucc_inj.
Qed. 

(** ** EIII-3-5 Exponentiation of cardinals *)

Definition cpow a b := cardinal (functions b a).
Notation "x ^c y" := (cpow x y) (at level 30).

Lemma CS_pow a b: cardinalp (a ^c b).
Proof. apply:CS_cardinal. Qed.

Global Hint Resolve CS_pow: fprops.

Lemma cpow_pr0 a b: a ^c b = cardinal (gfunctions b a).
Proof. by apply/card_eqP; apply:Eq_fun_set. Qed.
  
Lemma cpow_pr a b a' b':
  a =c a' -> b =c b' -> a ^c b = a' ^c b'.
Proof. 
move=> /card_eqP[f [bf sf tf]] /esym /card_eqP[g [bg sg tg]]; apply /card_eqP.
exists (compose3function g f); hnf.
rewrite {2 3} /compose3function - sf -tf - sg -tg; aw. 
by split => //;apply: c3f_fb.
Qed.

Lemma cpowcl a b: (cardinal a) ^c b = a ^c b. 
Proof. by apply: cpow_pr;aw. Qed.

Lemma cpowcr a b: a ^c (cardinal b) = a ^c b. 
Proof. by apply: cpow_pr; aw. Qed.

Theorem cpow_pr1 x y: 
  cardinal (functions y x) = (cardinal x) ^c (cardinal y). 
Proof. by apply: cpow_pr; aw. Qed.

Theorem cprod_of_same a b:  
  cprodb b (fun i: Set => a) = a ^c b.
Proof. 
rewrite cpow_pr0 /cprodb /cprod (setXb_eq_gfunctions (x:=a)); aw; trivial.
by move   => i ib; rewrite LgV.
Qed.
 
Lemma cpow_sum a f:
  a ^c (csum f) = cprodb (domain f) (fun i => a ^c  (Vg f i)).
Proof. 
transitivity (a ^c (disjointU (Lg (domain f) (Vg f)))). 
  by apply: cpow_pr => //; rewrite - (csum_gr) /csumb /csum; aw.
rewrite -cprod_of_same {1}/cprodb /disjointU.
set S:= disjointU_fam _; set f0:= Lg _ _.
have pfa:partition_w_fam S (domain f0). 
  by move: (partition_disjointU (Lg (domain f) (Vg f))); rewrite /f0; aw. 
rewrite (cprod_An pfa) /S /disjointU_fam ! Lgd;apply cprodb_exten.
move=> x xdf; rewrite !LgV // /cprodb - cpowcr -(cardinal_indexed (Vg f x) x).
rewrite cpowcr - cprod_of_same; congr cprod.
apply: Lg_exten => t tw. rewrite LgV //.
apply /setUb_P; rewrite /S /disjointU_fam; aw; ex_tac;rewrite !LgV//.
Qed.

Lemma cpow_prod b f: 
  (cprod f) ^c b = cprodb (domain f) (fun i => (Vg f i) ^c b).
Proof. 
move: (cprod_An2 (domain f) b (fun i j=> Vg f i )).
set A := cprodb _ _.
have ->  : cprodb (domain f) (fun i => Vg f i ^c b)= A.
  by apply: cprodb_exten => i idf; rewrite - cprod_of_same.
by move ->; rewrite - cprod_of_same;apply:cprodb_exten => i _; rewrite cprod_gr.
Qed.

Lemma cpow_sum2 a b c:  a ^c (b +c c) = (a ^c b) *c (a ^c c).
Proof.  by rewrite cpow_sum variantLc_d cprod2_pr0; aw. Qed.

Lemma cpow_prod2 a b c:  (a *c b) ^c c =  (a ^c c) *c (b ^c c).
Proof. by rewrite cpow_prod variantLc_d cprod2_pr0; aw. Qed.

Lemma cpow_pow a b c:  a ^c (b *c c) = (a ^c b) ^c c.
Proof. 
rewrite -csum_of_same cpow_sum - cprod_of_same. aw.
apply:cprodb_exten => x xc; rewrite LgV //.
Qed.

Lemma cpowx0 a: a ^c \0c =  \1c.
Proof. by rewrite /cpow functions_empty cardinal_set1. Qed.

Lemma cpow00: \0c ^c \0c =  \1c.
Proof. apply: cpowx0. Qed.

Lemma cpowx1c a: a ^c \1c = cardinal a.
Proof. 
by rewrite -cpowcl - cprod_of_same (cprod_trivial3) double_cardinal.
Qed.

Lemma cpowx1 a: cardinalp a -> a ^c \1c = a.
Proof. by move=> /card_card ac; rewrite cpowx1c. Qed.

Lemma cpow1x a: \1c ^c a = \1c.
Proof. 
move: fgraph_set0 domain_set0 => eg de.
by rewrite - (cprod_trivial de) cpow_prod // de /cprodb /Lg funI_set0.
Qed. 

Lemma cpow0x a: a <> \0c -> \0c ^c a = \0c.
Proof. 
move => /nonemptyP [x xa];rewrite - cprod_of_same.
apply: cprod_eq0; exists x; aw;trivial; rewrite LgV //; exact: cardinal_set0.
Qed.

Lemma cpowx2 a:  a ^c \2c = a *c a.
Proof. by rewrite - csum_11 cpow_sum2 cpowx1c cprod2cl cprod2cr. Qed.

Definition char_fun A B := Lf (varianti A \1c \0c)  B C2.

Lemma char_fun_axioms  A B: 
  lf_axiom (varianti A \1c \0c) B C2.
Proof. move=> z zB; rewrite /varianti;Ytac zA; fprops. Qed.

Lemma char_fun_f A B: function (char_fun A B).
Proof. rewrite/char_fun; apply: lf_function; apply: char_fun_axioms. Qed.

Lemma char_fun_V  A B x :
  inc x B -> Vf (char_fun A B) x = (varianti A \1c \0c x).
Proof. move=> xB; rewrite /char_fun LfV //; apply: char_fun_axioms. Qed.

Lemma char_fun_V_cardinal A B x:
  inc x B -> cardinalp (Vf (char_fun A B) x).
Proof. 
move => h; rewrite (char_fun_V A h) /varianti; Ytac h'; fprops.
Qed.

Lemma char_fun_V_a A B x: sub A B -> inc x A ->
  Vf (char_fun A B) x = \1c.
Proof. 
move=> AB xA; rewrite (char_fun_V A  (AB _ xA)).
by apply: varianti_in.
Qed. 

Lemma char_fun_V_b  A B x:  sub A B -> inc x (B -s A) ->
  Vf (char_fun A B) x = \0c.
Proof. 
move=> AB /setC_P [xB nxA]; rewrite (char_fun_V _ xB).
by apply: varianti_out.
Qed.

Lemma char_fun_injectiveP A A' B: sub A B -> sub A' B ->
  ((A=A') <-> (char_fun A B = char_fun A' B)).
Proof. 
move=> AB A'B; split => scf; first by rewrite scf.
set_extens x => xs; ex_middle u. 
  have xc:= (char_fun_V_b A'B (setC_i (AB _ xs) u)).
  by case: card1_nz; rewrite -(char_fun_V_a AB xs) scf.
have xc:= (char_fun_V_b AB (setC_i (A'B _ xs) u)).
by case: card1_nz; rewrite -(char_fun_V_a A'B xs) - scf.
Qed.

Lemma char_fun_surjective X f: function_prop f X C2 ->
  exists2 A, sub A X & char_fun A X = f.
Proof.
move => [fy <- ty].
set W := Zo (source f) (fun z => Vf f z = \1c).  
have WX: sub W (source f) by apply: Zo_S.
exists W => //.
symmetry;rewrite/char_fun;apply: function_exten => //; aw; trivial.
  apply: char_fun_f.
move => s sX /=; case: (inc_or_not s W) => ws.
  rewrite (char_fun_V_a WX ws); exact: (Zo_hi ws).
rewrite (char_fun_V_b WX (setC_i sX ws)).
move: (Vf_target fy sX); rewrite ty.
by case /set2_P => // f1; case: ws; apply/Zo_P.
Qed.

Theorem card_setP X: cardinal (\Po X) = \2c ^c X.
Proof.
set K:= functions X \2c.
apply/card_eqP; exists (Lf (char_fun ^~ X) (\Po X) K); hnf;saw.
apply:lf_bijective.
- move => y /setP_P yX; apply /functionsP;split => //; rewrite /char_fun; aww.
  by apply:char_fun_f.
- by move => u v /setP_P uX /setP_P vX /(char_fun_injectiveP uX vX).
- move => y /functionsP /char_fun_surjective  [A /setP_P pa pb]; ex_tac.
Qed.


(** ** EIII-3-6 Order relation and operations on cardinals *)


Definition cdiff a b := cardinal (a -s b).
Notation "x -c y" := (cdiff x y) (at level 50).

Lemma CS_diff a b: cardinalp (a -c b).
Proof. apply CS_cardinal. Qed.

Lemma cardinal_setC A E: sub A E ->
  (cardinal A) +c (E -c A)  = cardinal E.
Proof.
by move=> AE; rewrite /cdiff csum2cl csum2cr - cardinal_setC2.
Qed.

Lemma cdiff_pr a b: a <=c b -> a +c (b -c a) = b.
Proof.
move=> [cb ca sab].
by rewrite -{1} (card_card cb) cardinal_setC // (card_card ca).
Qed.

Lemma csum_M0le a b: cardinalp a -> a <=c (a +c b).
Proof.
move => ca; rewrite - {1} (card_card  ca) - (card_card (CS_sum2 a b)).
move:(sub_smaller (@subsetU2l  (a *s1 C1) (b *s1 C0))).
by rewrite - (disjointU2_pr3 a b C0_ne_C1) cardinal_indexed.
Qed. 

Theorem cardinal_le_setCP  a b:
  cardinalp a -> cardinalp b ->
  ((b <=c a) <-> (exists2 c, cardinalp c & b +c c = a)).
Proof. 
move=> ca cb; split.
  by move/cdiff_pr => H; exists (a -c b) => //; apply: CS_diff. 
by move=> [c cc <-]; apply:csum_M0le.
Qed. 

Theorem csum_increasing f g:
  domain f = domain g -> 
  (forall x, inc x (domain f) -> (Vg f x) <=c (Vg g x)) ->
  (csum f) <=c (csum g).
Proof. 
move=> dfdg ale; apply: sub_smaller => t.
rewrite /disjointU /disjointU_fam.
move /setUb_P; aw; move => [y ydf];  rewrite LgV //. 
move /setX_P => [pt Pt /set1_P Qt]; apply/setUb_P; aw; rewrite -dfdg.
ex_tac; rewrite LgV // -{2} Qt;apply :setX_i; fprops.
by move: (ale _ ydf) => [_ _];apply.
Qed.


Lemma csum_increasing0 I (f g: fterm):
  (forall x, inc x I -> f x <=c g x) ->
  (csumb I f) <=c (csumb I  g).
Proof. 
move=> ale;apply:csum_increasing; aw;trivial => i idx.  
by rewrite !LgV //; apply: ale.
Qed.


Theorem cprod_increasing f g:
  domain f = domain g -> 
  (forall x, inc x (domain f) -> (Vg f x) <=c (Vg g x)) ->
  (cprod f) <=c (cprod g).
Proof. 
move=> dfdg alle.
by apply: sub_smaller; apply: setXb_monotone1 =>// i /alle [_ _].
Qed. 


Lemma cprod_increasing0 I (f g: fterm):
  (forall x, inc x I -> f x <=c g x) ->
  (cprodb I f) <=c (cprodb I g).
Proof. 
move=> ale; apply:cprod_increasing; aw; trivial => i idx.
by rewrite !LgV //; apply: ale.
Qed.


Lemma cardinal_uniona X n:  (forall x, inc x X -> cardinal x <=c n) ->
  cardinal (union X) <=c n *c cardinal X.
Proof.
move => h.
set A := Lg (domain (identity_g X))(fun a => cardinal (Vg (identity_g X) a)).
set B := cst_graph X n.
have  sd: domain A = domain B by  rewrite /A/B identity_d; aw.
have le:(forall x, inc x (domain A) -> Vg A x <=c Vg B x).
  rewrite /A/B Lgd identity_d => x xX; rewrite !LgV //; fprops.
rewrite cprod2cr - csum_of_same.
apply: cleT (csum_increasing sd le).
by  move: (csum_pr1 (identity_g X));rewrite setUb_identity.  
Qed.

Lemma csum_increasing1 f j: 
  sub j (domain f) -> (csum (restr f j)) <=c (csum f).
Proof. 
move=> sjd.
apply: sub_smaller => t. 
rewrite /disjointU /disjointU_fam - setU_bf - setU_bf restr_d.
move /setUf_P => [y yd]; rewrite LgV // => tp.
apply /setUf_P; move: (sjd _ yd) => yf; ex_tac.
Qed.

Lemma cprod_increasing1 f j:  card_nz_fam f ->
  sub j (domain f) -> (cprod (restr f j)) <=c (cprod f).
Proof. 
move=> alne sjd; rewrite cprod_pr cprod_pr /cprodb; aw.
set f' := Lg (domain f) (fun z => cardinal (Vg f z)).
pose (g:= Lg (domain f)  (fun z => Yo (inc z j) (cardinal (Vg f z)) \1c)).
have fgg: fgraph g by rewrite /g; fprops.
have dgdf : domain g = domain f by rewrite /g; aw.
have ->: (Lg j (fun a : Set => cardinal (Vg (restr f j) a))) = Lg j (Vg g).
  by apply: Lg_exten => a aj;rewrite /g !LgV// ; [ Ytac0 | apply: sjd].
have <-: (cprod g = cprod (Lg j (Vg g))).
  apply: cprod_one_unit=>//; rewrite dgdf //. 
  by move=> i /setC_P [idf nij]; rewrite /g LgV // Y_false.
rewrite/g/f';apply: cprod_increasing; aw; trivial.
move => x xdg;  rewrite !LgV //; Ytac h; fprops.
apply: cge1; fprops; exact:(card_nonempty0  (alne x xdg)).
Qed. 


Lemma csum_increasing6 f j:  cardinalp (Vg f j) ->
  inc j (domain f) -> (Vg f j) <=c (csum f).
Proof. 
move=> cf jd.
move: (csum_increasing1 (set1_sub jd)).
by rewrite csum_trivial4 (card_card cf).
Qed.

Lemma cprod_increasing6 f j:  cardinalp (Vg f j) -> card_nz_fam f ->
  inc j (domain f) -> (Vg f j) <=c (cprod f).
Proof.
move=> cf alnz jd.
move: (cprod_increasing1 alnz (set1_sub jd)).
by rewrite cprod_trivial4 (card_card cf).
Qed.

Lemma csum_Mlele a b a' b':
  a <=c a' -> b <=c b' -> (a +c b) <=c (a' +c b').
Proof. 
by move=> aa' bb'; apply: csum_increasing; aww => x xtp; try_lvariant xtp.
Qed. 

Lemma csum_Meqle a b b': b <=c b' -> (a +c b) <=c (a +c b').
Proof.
move => h; rewrite -(csum2cl a b) -(csum2cl a b').
apply:csum_Mlele; fprops.
Qed. 

Lemma csum_Mleeq a b b': b <=c b' -> (b +c a) <=c (b' +c a).
Proof. by move => h; rewrite (csumC _ a)(csumC _ a); apply: csum_Meqle. Qed.

Lemma cprod_Mlele a b a' b':
  a <=c a' -> b <=c b' -> (a *c b) <=c (a' *c b').
Proof. 
by move=> aa' bb';apply: cprod_increasing;aww => x xtp; try_lvariant xtp.
Qed.

Lemma cprod_Meqle a b b': b <=c b' -> (a *c b) <=c (a *c b').
Proof.
move => h; rewrite -(cprod2cl a b) -(cprod2cl a b').
apply:cprod_Mlele;fprops.
Qed. 

Lemma cprod_Mleeq a b b': b <=c b' -> (b *c a) <=c (b' *c a).
Proof. by move => h; rewrite (cprodC _ a)(cprodC _ a); apply: cprod_Meqle. Qed.

Lemma csum_Mle0 a b: cardinalp a -> a <=c (b +c a).
Proof. by rewrite csumC; apply:csum_M0le. Qed. 

Lemma csum2_pr6 a b: cardinal (a \cup b) <=c a +c b.
Proof.
rewrite - (setU2Cr2 a b) (csum2_pr5 (set_I2Cr b a)) - (csum2cr a b).
rewrite - (csum2cr a); apply: csum_Meqle; apply: sub_smaller; apply: sub_setC.
Qed.
 
Lemma cprod_M1le a b: cardinalp a ->
  b <> \0c -> a <=c (a *c b).
Proof. 
move=> ca nbz. 
rewrite -{1}(cprod1r ca) - (cprod2cr a b).
apply: cprod_Mlele; fprops; apply: cge1; fprops.
by apply: card_nonempty0.
Qed.

Lemma csum_eq1 a b: cardinalp a -> cardinalp b -> a +c b = \1c ->
    (a = \0c \/ b = \0c).
Proof.
move => ca cb eq.
case: (equal_or_not a \0c) => anz; first by left.
case: (equal_or_not b \0c) => bnz; first by right.
move:(csum_Mlele (cge1 ca anz) (cge1 cb bnz)).
by rewrite csum_11 eq => /(cltNge clt_12).
Qed.

Lemma cprod_eq1 a b: cardinalp a -> cardinalp b -> a *c b = \1c ->
    (a = \1c /\ b = \1c).
Proof.
move => ca cb eq.
case: (equal_or_not a \0c) => az.
  by move: eq; rewrite az cprod0l => bad; case: card1_nz.
case: (equal_or_not b \0c) => bz.
  by move: eq; rewrite bz cprod0r => bad; case: card1_nz.
case: (equal_or_not a \1c) => px1; first by rewrite - {2} eq px1 (cprod1l cb).
move: (cprod_Mlele (cge2 ca az px1) (cge1 cb bz)). 
by rewrite (cprod1r CS2) eq => /(cltNge clt_12).
Qed.

Lemma cpow_Mleeq x y z: x <=c y -> x <> \0c -> x ^c  z <=c y ^c z.
Proof.
move=> xy xz.
by rewrite - cprod_of_same - cprod_of_same; apply: cprod_increasing0 => _ _.
Qed.

Lemma cpow_Meqle x a b:
  x <> \0c -> a <=c b -> x ^c a <=c x ^c b.
Proof. 
move => /card_nonempty0 xnz /proj33 leab.
rewrite - cpowcl -(cpowcl x b) - 2! cprod_of_same /cprodb.
rewrite - (restr_Lg  (fun _  => (cardinal x)) leab).
apply: cprod_increasing1;hnf; aw; trivial => z zx;  rewrite LgV //; fprops.
Qed.

Lemma cpow_Mlele a b a' b':
  a <> \0c -> a <=c a' -> b <=c b' ->  (a ^c b) <=c (a' ^c b').
Proof. 
move=> nz aa' bb'; apply: (cleT (cpow_Mleeq b aa' nz)).
by apply:cpow_Meqle bb'; dneg az; apply:cle0; rewrite -az.
Qed.

Lemma cpow_M2le x y: x <=c y -> \2c ^c x <=c \2c ^c y.
Proof. move=> h; apply: cpow_Meqle; fprops. Qed.

Lemma cpow_Mle1 a b: 
  cardinalp a -> b <> \0c  -> a <=c (a ^c b).
Proof. 
move=> ca  l1b.
case: (equal_or_not a \0c); first by move => ->; apply: cle0x; fprops.
move=> anz;rewrite - cpowcr - {1} (cpowx1 ca); apply:(cpow_Meqle anz).
by apply:(cge1 (CS_cardinal b)); apply: card_nonempty0.
Qed.

Theorem cantor a: cardinalp a -> a <c (\2c ^c a).
Proof. 
move=> ca; rewrite - card_setP. 
rewrite - {1} (card_card ca). 
split.
  apply /eq_subset_cardP1.
  exists (Lf singleton a (\Po a)); hnf; saw. 
  apply: lf_injective. 
    by move=> t ta /=; apply/setP_P => v /set1_P ->.
  by move=> u v ua va; apply: set1_inj.
apply/ card_eqP; move => [f [[_ suf] sf tf]].
set (X:= Zo a (fun x => (~ inc x (Vf f x)))). 
have Xt: (inc X (target f)) by rewrite tf; apply /setP_P; apply: Zo_S.
move: ((proj2 suf) _  Xt) => [y ysf Wy].
have:(~ (inc y X)) by move=> yX; move: (yX) => /Zo_hi;rewrite - Wy.
move=> h;case: (h); apply: Zo_i; ue.
Qed.

Lemma infinite_pow2 x: infinite_c x -> infinite_c (\2c ^c x). 
Proof.
move => oo; exact (cle_inf_inf oo (proj1 (cantor (proj1 oo)))). 
Qed.

Lemma cantor_bis: non_coll cardinalp.
Proof.
move=> [a ap].
have ca: cardinal_set a by move => t /ap.
case: (cltNge (cantor (CS_sup ca))); apply: (card_sup_ub ca); apply/ap; fprops.
Qed.


Definition cnext c := Zo (\2c ^c c) (fun z => cardinal z <=c c).

Lemma cnextP c: cardinalp c -> forall x,
  (inc x (cnext c) <-> (ordinalp x /\ cardinal x <=c c)).
Proof.
move => cc x.
move:(cantor cc) => ncc; move: (ncc) => [[_ cc1 _] _]; move: (cc1) => [oc _].
split; first by move /Zo_P =>[/(Os_ordinal oc) h1 h2].
move => [h1 h2];apply: Zo_i => //.
move: (cle_ltT h2 ncc) => h3.
by move /(ocle2P cc1 h1): h3 => /oltP0 [].
Qed.

Lemma cnext_pr1 c (a:= cnext c): cardinalp c ->
 [/\ cardinalp a, c <c a & forall c', c <c c' -> a <=c c'].
Proof.
move => cc.
have H:= (cnextP cc). 
have ose: ordinal_set a by move => t /H [pa _].
have oe: ordinalp a.
  apply: ordinal_pr => // t /H [pa pb] s st.
  apply/H; split; first exact: (Os_ordinal pa st).
  exact:(cleT  (sub_smaller (ordinal_transitive pa st)) pb).
case: (cleT_el (CS_cardinal a) cc) => pa.
  by case /H: (ordinal_irreflexive oe).
have pb: forall c', c <c c' -> sub a c'.
  move => c' cc'; move:(proj32_1 cc') => h2 t /H [sa sb].
  by move /(ocle2P h2 sa): (cle_ltT sb cc') => /olt_i.
have cp: cardinalp a.
  split => // z  oz /card_eqP hh; rewrite hh in pa.
  move: (card_ord_le oz) => [_ _ s3]; exact: (sub_trans  (pb _ pa) s3).
rewrite -{2} (card_card cp); split => //.
by move => c' cc'; split => //; [ exact:proj32_1 cc' | apply: pb].
Qed.

Lemma CS_cnext x: cardinalp x -> cardinalp (cnext x).
Proof. by move/cnext_pr1 /proj31. Qed.

Lemma cnext_pr4 x y: cardinalp y -> x <c cnext y -> x <=c y.
Proof.
move => pa pb.
case: (cleT_el (proj31_1 pb) pa) => // h.
case: (cltNge pb (proj33 (cnext_pr1 pa) _ h)).
Qed.

Lemma cnext_pr2 x: cardinalp x -> x <c cnext x.
Proof. by move=> ic; exact (proj32 (cnext_pr1 ic)). Qed.

Lemma cnext_pr3 x: cardinalp x ->  cnext x <=c \2c ^c x.
Proof. 
by move=> ic; move: (cnext_pr1 ic) => [pa pb]; apply; apply: cantor.
Qed.

Lemma cnext_pr5P x : cardinalp x -> 
   forall y, (x <c y <-> cnext x <=c y).
Proof.
move => cx; split => h.
  by apply: (proj33 (cnext_pr1 cx)).
exact:(clt_leT (cnext_pr2 cx) h).
Qed.

Lemma cnext_pr4P y: cardinalp y -> 
   forall x, (x <c cnext y <-> x <=c y).
Proof.
move => cy x; split; first by apply: cnext_pr4. 
move => sb; exact:(cle_ltT sb (cnext_pr2 cy)).
Qed.

Lemma cnext_pr6 x y: x <=c y -> cnext x <=c cnext y.
Proof.
move => xy.
move: (xy) => [cx cy _].
by apply/cnext_pr5P => //; apply/cnext_pr4P.
Qed.

End CardinalOps.
Export CardinalOps.

Module FiniteSets.

(** ** EIII-4-1 Definition of integers *)

Definition Nat := omega0. 

Definition natp x := inc x Nat.

Theorem finite_succP x:  cardinalp x ->
  (finite_c (csucc x) <-> finite_c x).
Proof. 
case /finite_or_infinite. 
  move => h; rewrite (succ_of_finite h); exact: finite_sP.
by move /csucc_inf => <-.
Qed.

Lemma infinite_Nat: infinite_set Nat.
Proof. hnf; rewrite (card_card CS_omega); exact OIS_omega. Qed.

Lemma NatP a: natp a  <-> finite_c a.
Proof. exact: omega_P2. Qed.

Lemma Nat_i a: finite_c a -> natp a.
Proof. by move /NatP. Qed.

Lemma Nat_hi a: natp a -> finite_c a.
Proof. by move /NatP. Qed.

Global Hint Resolve Nat_i Nat_hi: fprops.

Lemma CS_nat x: natp x -> cardinalp x.
Proof. fprops. Qed.

Lemma card_nat n: natp n -> cardinal n = n.
Proof. by move/CS_nat/card_card. Qed.

Lemma cle0n n: natp n -> \0c <=c n.
Proof. by move => /CS_nat /cle0x. Qed.
  
Lemma finite_set_nat n: natp n -> finite_set n.
Proof. 
by move => nN; rewrite /finite_set (card_nat nN); apply/NatP.
Qed.

Lemma NS_succ x: natp x -> natp (csucc x).
Proof. by move => /NatP h;rewrite (succ_of_finite h); apply/NatP/finite_sP. Qed.

Lemma NS_nsucc x: cardinalp x -> natp (csucc x) -> natp x.
Proof. by  move => xs /NatP/(finite_succP xs) /NatP. Qed.

Global Hint Resolve CS_nat : fprops.
Global Hint Resolve NS_succ: fprops.

Lemma Nsucc_rw x: natp x -> csucc x = x +c \1c.
Proof. by move=> fx; apply: csucc_pr4; fprops. Qed.

Lemma succ_of_nat n: natp n -> csucc n = osucc n.
Proof. by move => /NatP nN;rewrite succ_of_finite. Qed.

Lemma OS_nat x: natp x -> ordinalp x.
Proof. by move =>  /CS_nat /OS_cardinal. Qed. 

Lemma NS_inc_nat a: natp a -> forall b, inc b a -> natp b.
Proof. move => ha; apply:(ordinal_transitive OS_omega ha). Qed.

Lemma Nsum0r x: natp x -> x +c \0c = x.
Proof. by move=> xN; apply: csum0r; fprops. Qed.

Lemma Nsum0l x: natp x -> \0c +c x = x.
Proof. by move=> xN; apply: csum0l; fprops. Qed.

Lemma Nprod1l x: natp x -> \1c *c x = x.
Proof. by move=> xN; apply: cprod1l; fprops. Qed.

Lemma Nprod1r x: natp x -> x *c \1c = x.
Proof. by move=> xN; apply: cprod1r; fprops. Qed.

Lemma NS_lt_nat a b: a <c b -> natp b -> natp a.
Proof. by move/oclt/olt_i => ha hb; apply:(NS_inc_nat hb ha). Qed.

Lemma NS_le_nat a b: a <=c b -> natp b -> natp a.
Proof.
by case/cle_eqVlt; [ move -> | apply:NS_lt_nat]. Qed.

Lemma olt_omegaP x: x <o omega0 <-> natp x.
Proof. apply: (oltP OS_omega). Qed.

Lemma clt_omegaP x: x <c omega0 <-> natp x.
Proof.
split => h; first by move: (oclt h) => /olt_omegaP.
by apply: oclt3; [fprops| apply: CS_omega | apply /olt_omegaP].
Qed.

Lemma Nat_dichot x: cardinalp x -> natp x \/ infinite_c x.
Proof. by move=> h; case: (finite_or_infinite h); [ move/NatP; left | right]. Qed.

Lemma Nat_le_infinite a b: natp a -> infinite_c b -> a <=c b.
Proof. by move/NatP; apply: cle_fin_inf. Qed.

Lemma Nmax_p1 x y: natp x -> natp y ->
  [/\ natp (cmax x y), x <=c (cmax x y) & y <=c (cmax x y)].
Proof.
move => xN yN.
have ha : natp (cmax x y) by apply:Gmax_E.
by move:(cmax_p1 (CS_nat xN) (CS_nat yN)) => [hb hc].
Qed.

Lemma NltP a: natp a -> forall x, x <c a <-> inc x a.
Proof.
move => aN x; split; first by move /oclt; apply: olt_i.
move => xa.
apply: (oclt3 (CS_nat (NS_inc_nat aN xa)) (CS_nat aN)).
by apply/(oltP (OS_nat aN)).
Qed.

Lemma NleP a: natp a -> forall x,
  (x <=c a <-> inc x (csucc a)).
Proof.
move=> aN x; rewrite (succ_of_nat aN).
split; first by move=> /ocle/(oleP (OS_nat aN)).
case/setU1_P;first by case/(NltP aN).
move => ->; apply: (cleR (CS_nat aN)).
Qed.

Lemma Nsucc_i a: natp a -> inc a (csucc a).
Proof. move => aN; rewrite (succ_of_nat aN); fprops. Qed.

Lemma least_cardinal2 (p : property):
  (forall b, natp b -> (forall x, x <c b -> p x) -> p b) ->
  forall a, natp a -> p a.
Proof.
move => H a aN.
move: (OS_nat aN) => oa; move: a oa aN; apply: least_ordinal2.
move => b ob Hb bN; apply:(H b bN) => x xlb.
exact:(Hb x (oclt xlb) (NS_lt_nat xlb bN)).
Qed.  

Lemma Nat_decent n: natp n -> ~(inc n n).
Proof.  apply: (ordinal_decent OS_omega). Qed. 

Definition card_three := csucc card_two.
Definition card_four := csucc card_three.
Notation "\3c" := card_three.
Notation "\4c" := card_four.

Lemma NS0: natp \0c.
Proof. apply: Nat_i; apply: finite_zero. Qed.

Lemma NS1: natp \1c.
Proof. move: NS0; rewrite - succ_zero; fprops. Qed.

Lemma NS2: natp \2c.
Proof. move: NS1; rewrite - succ_one; fprops. Qed.

Lemma NS3: natp \3c.
Proof. move: NS2; rewrite /card_three; fprops. Qed.

Lemma NS4: natp \4c.
Proof. move: NS3; rewrite /card_four; fprops. Qed.

Global Hint Resolve NS0 NS1 NS2: fprops.


Lemma finite_0: finite_c \0c.
Proof. fprops. Qed.

Lemma finite_1: finite_c \1c.
Proof. fprops. Qed.

Lemma finite_2: finite_c \2c.
Proof. fprops. Qed.

Global Hint Resolve finite_0 finite_1 finite_2 : fprops.

Lemma csum_22: \2c +c \2c = \4c.
Proof.
rewrite /card_four  (Nsucc_rw NS3).
rewrite /card_three (Nsucc_rw NS2)  - csumA - csum_11 //. 
Qed.

Lemma cprod_22: \2c *c \2c = \4c.
Proof. by rewrite - csum_22 csum_nn. Qed.

Lemma cpow_24: \2c ^c \4c = \4c ^c \2c.
Proof.
by rewrite -{2} cprod_22 cpow_prod2 - csum_22  cpow_sum2. 
Qed.

Lemma cardinal_tripleton x y z: x <> y -> x <> z -> y <> z ->
  cardinal (tripleton x y z) = \3c.
Proof. 
move => xy xz yz. rewrite /tripleton csucc_pr ? cardinal_set2 //.
by case /set2_P; apply: nesym.
Qed.

Lemma cardinal_ge3 E:  \3c <=c cardinal E ->
  exists a b c, 
  [/\ inc a E, inc b E, inc c E & [/\  a <> b, a <> c & b <> c]].
Proof.
rewrite /card_three - (card_card (CS_succ \2c)) (succ_of_nat NS2).
move /eq_subset_cardP1  => [f [[ff injf] sf tf]].
exists (Vf f \0c); exists (Vf f \1c); exists (Vf f \2c).
have zs: inc \0c (source f) by rewrite sf; apply /set3_P; in_TP4.
have os: inc \1c (source f) by rewrite sf; apply /set3_P; in_TP4.
have ts: inc \2c (source f) by rewrite sf; apply /set3_P; in_TP4.
rewrite -tf;split; fprops; split=> h.
by move: (injf _ _ zs os h); fprops.
by move: (injf _ _ zs ts h); fprops.
by move: (injf _ _ os ts h); fprops.
Qed.

Lemma cardinal_doubleton x y: cardinal (doubleton x y) <=c \2c.
Proof.
case: (equal_or_not x y) => eq.
  rewrite eq; rewrite cardinal_set1; apply: cle_12.
rewrite (cardinal_set2 eq); fprops.
Qed.

Lemma NS_in_suml a b: cardinalp a -> natp (a +c b) -> natp a.
Proof. move => /(csum_M0le b) sa; exact:NS_le_nat.  Qed.

Lemma NS_in_sumr a b: cardinalp b -> natp (a +c b) -> natp b.
Proof. rewrite csumC;exact:NS_in_suml. Qed.

Lemma NS_in_product a b: cardinalp a -> 
  b <> \0c -> natp (a *c b) -> natp a.
Proof. 
move=> ca nzb. 
have on: (\1c <=c (cardinal b)). 
  apply: cge1; [fprops | by apply: card_nonempty0].
rewrite -(cprod2cr a b) -(cdiff_pr on) cprodDr (cprod1r ca).
apply: (NS_in_suml ca). 
Qed.

Lemma cdiff_le1 a b: cardinalp a -> a -c b <=c a.
Proof.
by move => /card_card h; move: (sub_smaller (@sub_setC a b)); rewrite h.
Qed.

Lemma cdiff_nz a b:  b <c a -> (a -c b) <> \0c.
Proof.
move => [lea nea] cs; case: nea. 
by rewrite -(cdiff_pr lea) cs (csum0r (proj31 lea)).
Qed.

Lemma NS_diff a b: natp a -> natp (a -c b).
Proof.
move => h; apply:(NS_le_nat (cdiff_le1 b (CS_nat h)) h).
Qed.

Global Hint Resolve  NS_diff: fprops.

Definition cpred := opred. 

Lemma cpred0 : cpred \0c = \0c.
Proof. exact: setU_0. Qed.

Lemma cpred1: cpred \1c = \0c.
Proof.
by move: (succo_K OS0); rewrite osucc_zero.
Qed.

Lemma cpred_inf a: infinite_c a -> cpred a = a.
Proof. by  move/ infinite_card_limit1. Qed.

Lemma cpred_pr n: natp n -> n <> \0c ->
  (natp (cpred n) /\  n = csucc (cpred n)).
Proof.
move=>/NatP nN nz; move: (finite_pred nN nz) => [y /NatP yN ->].
by rewrite /cpred (succo_K (OS_nat yN)) (succ_of_nat yN).
Qed.

Lemma NS_pred a: natp a -> natp (cpred a).
Proof.
move => aN; case: (equal_or_not a \0c) => az.
  by rewrite az cpred0 -az.
exact: (proj1 (cpred_pr aN az)).
Qed.

Lemma CS_pred a: cardinalp a -> cardinalp (cpred a).
Proof. 
move => h; case: (Nat_dichot h); first by move/NS_pred/CS_nat.
by move/(cpred_inf) => ->.
Qed.

Lemma cpred_pr2 n: natp n -> cpred (csucc n) = n.
Proof.
by move => nN; rewrite (succ_of_nat nN); apply: succo_K; apply: OS_nat.
Qed.

Lemma cpred_pr1 n: cardinalp n -> cpred (csucc n) = n.
Proof. 
case /Nat_dichot; first by move/cpred_pr2. 
by move => ifn;move: (ifn) => /csucc_inf <-; apply: cpred_inf.
Qed.

Lemma cpred_pr5 x y: inc x y -> cpred (cardinal y) = cardinal (y -s1 x).
Proof. move/csucc_pr2 => ->; apply: cpred_pr1; fprops. Qed. 

Lemma cpred_nz n: cardinalp n -> cpred n <> \0c -> \0c <c cpred n. 
Proof. move => pa pb; exact:(card_ne0_pos (CS_pred pa) pb). Qed.

Lemma cpred_le a: cardinalp a -> cpred a <=c a.
Proof. 
move => ca; apply: (ocle3 (CS_pred ca) ca (opred_le (proj1 ca))).
Qed.

Lemma cpred2: cpred \2c = \1c.
Proof. by rewrite - succ_one (cpred_pr2 NS1). Qed.

Lemma cleS0 a: cardinalp a -> a <=c (csucc a). 
Proof. by move=> ca; rewrite (csucc_pr4 ca); apply: csum_M0le. Qed.

Lemma cleS a: natp a -> a <=c (csucc a).
Proof. by move=> /CS_nat /cleS0. Qed.

Lemma cltS a: natp a -> a <c (csucc a).
Proof. by move => aN; apply/(NltP (NS_succ aN)); apply: Nsucc_i. Qed.

Global Hint Resolve cleS cltS: fprops.

Lemma cle_24: \2c <=c \4c.
Proof. exact: (cleT (cleS NS2)(cleS NS3)). Qed.

Lemma clt_24: \2c <c \4c.
Proof. exact: (cle_ltT (cleS NS2)(cltS NS3)). Qed.

Theorem cltSleP n: natp n -> forall a,
  (a <c (csucc n) <-> a <=c n).
Proof.
move => nN a.
apply:(iff_trans (NltP (NS_succ nN) a) (iff_sym (NleP nN a))).
Qed.

Lemma cleSS a b : a <=c b -> csucc a <=c csucc b. 
Proof.
move => h; move:(h) => [ca cb _].
rewrite ! csucc_pr4 //;apply: (csum_Mlele h (cleR CS1)).
Qed.

Lemma cleSSP a b: cardinalp a -> cardinalp b ->
  (csucc a <=c csucc b <-> a <=c b).
Proof. 
move => ca cb; split => h; last by apply: cleSS.
have le1 := (cleS0 ca); have le2 := (cleT le1 h).
case: (Nat_dichot cb) => bN; last by move/csucc_inf: bN => ->.
by move /(cltSleP bN):(clt_leT (cltS (NS_le_nat le2 (NS_succ bN))) h).
Qed.


Lemma cltSS a b : a <c b -> csucc a <c csucc b. 
Proof.
move => [pa pb]; split; first by apply:cleSS. 
by move/(csucc_inj (proj31 pa) (proj32 pa)).
Qed.

Lemma cltSSP n m: cardinalp n -> cardinalp m ->
  ((csucc n <c csucc m) <-> (n <c m)).
Proof.
move => cn cm; split; last by apply:cltSS.
move => [pa pb]; split; first by move/(cleSSP cn cm) : pa.
by move => h; case: pb; rewrite h.
Qed.


Lemma cleSlt0P a b: cardinalp a -> natp b ->
  (csucc a <=c b <-> a <c b).
Proof.
move => ca bN.
split => hyp.
  by apply/(cltSSP ca (CS_nat bN)); apply/(cltSleP bN).
by apply/(cltSleP bN) /(cltSSP ca (CS_nat bN)).
Qed.

Lemma cleSltP a: natp a -> forall b,
  (csucc a <=c b <-> a <c b).
Proof. 
move=> aN b.
case (p_or_not_p (cardinalp b)) => h; last first. 
   split => lt;case: h; [ exact :proj32 lt | exact :proj32_1 lt].
case: (Nat_dichot h) => H; first by apply /(cleSlt0P (CS_nat aN) H). 
split => _; first by apply:(clt_fin_inf (Nat_hi aN)).
apply:(cle_fin_inf (Nat_hi (NS_succ aN)) H). 
Qed.

Lemma cpred_pr6 k i: natp k -> \1c <=c i -> i <=c csucc k -> 
  [/\ natp (cpred i), i = csucc (cpred i) & cpred i <=c k].
Proof.
move => kN sa sb.
have inz : i <> \0c by move => iz; case:(cltNge clt_01); rewrite -iz.
move: (cpred_pr (NS_le_nat sb (NS_succ kN)) inz) => [ra rb]; split => //. 
by move: sb; rewrite {1} rb; move /(cleSSP (CS_nat ra)( (CS_nat kN))).
Qed.

Lemma cpred_lt n: natp n  -> n <> \0c -> cpred n <c n.
Proof.
move => nN nz.
move: (cpred_pr nN nz) =>[sa sb].
apply /(cleSltP sa); rewrite - sb; fprops.
Qed.

Lemma cmax_succ a b: cardinalp a -> cardinalp b -> 
  cmax (csucc a) (csucc b) = csucc (cmax a b).
Proof.
wlog: a b / a <=c b.
  move => H ca cb; case: (cleT_ee ca cb) => H'; first by apply:H.
  by rewrite (cmaxC ca cb)(cmaxC (CS_succ _) (CS_succ _)); apply: H.
by move => lab ca cb;rewrite /cmax/Gmax (Y_true (cleSS lab)) (Y_true lab).
Qed.

Lemma inf_Nat E (x:= intersection E): sub E Nat -> nonempty E ->
   inc x E /\ (forall y, inc y E -> x <=c y).
Proof.
by move => pa; apply:cle_wor' => // t /pa /CS_nat.
Qed.

Lemma NS_inf_Nat E (x:= intersection E): sub E Nat -> natp x.
Proof.
move => h; case (emptyset_dichot E) => h1.
  rewrite /x h1 setI_0; fprops.
exact: (h _ (proj1 (inf_Nat h h1))).
Qed.

Lemma least_int_prop n (p: property) (y:= least_ordinal p n): natp  n -> p n ->
   [/\ natp y, p y& forall z, natp z -> p z -> y <=c z].
Proof.
move => nN pn; move: (OS_nat nN) => on.
move: (least_ordinal4 on pn) => [ha hb hc].
move: (hc n on pn) => lyn.
have yN: natp y.
  by apply/ (oltP OS_omega); apply: (ole_ltT lyn);apply/ (oltP OS_omega).
split => // z zN pz;exact:(ocle3 (CS_nat yN) (CS_nat zN) (hc z (OS_nat zN) pz)).
Qed. 


Lemma least_int_prop2 n (p: property)
      (x:= cpred (least_ordinal p n)): natp  n -> p n ->
  p \0c \/ [/\ natp x, p (csucc x) & ~ p x].
Proof.
move => ha hb.
move: (least_int_prop ha hb) => [qa qb qc].
case: (equal_or_not (least_ordinal p n) \0c); first by move <-;left.
move => zp; right; move: (cpred_pr qa zp) => [qd qe]; rewrite - qe. split => //.
by move => px; case:(cleNgt(qc _ qd px)); rewrite {2} qe; apply: cltS.
Qed.

Lemma card_finite_setP x: finite_set x <-> natp (cardinal x).
Proof. apply: iff_sym;apply:NatP. Qed.

Lemma emptyset_finite: finite_set emptyset.
Proof. apply/NatP; rewrite cardinal_set0; apply: NS0. Qed.

Lemma finite_set_prop1 a y: inc a y ->
  ((cardinal (y -s1 a)) <> (cardinal y) <-> finite_set y).
Proof. 
move => ay.
rewrite/finite_set - (setC1_K ay) csucc_pr1 (setC1_K ay).
have cz := (CS_cardinal (y -s1 a)).
split; last by move/(finite_succP cz) /finite_cP/proj2.
by move=>h; apply/(finite_succP cz); apply/finite_cP.
Qed.


Lemma strict_sub_smaller y: 
  (forall x, ssub x y -> (cardinal x) <c (cardinal y)) <->
  finite_set y.
Proof. 
split => h.
  case: (emptyset_dichot y); first by move => ->; apply: emptyset_finite.
  move=> [a ay]; apply /(finite_set_prop1 ay).
  exact: (proj2(h _ (setC1_proper ay))).
move=> x ssxy.
move: (setC_ne ssxy) =>[u uc].
move /setC_P : uc => [uy ux].
move/(finite_set_prop1 uy): h => c1.
set (z := y -s1 u).
have /sub_smaller lexz: sub x z.
   apply/subsetC1_P; split => //; exact: (proj1 ssxy).
apply: (cle_ltT lexz); split => //; apply: sub_smaller; apply: sub_setC.
Qed.

Lemma strict_sub_smaller_contra x y: finite_set y -> sub x y ->
  cardinal x = cardinal y -> x = y.
Proof.
move => /strict_sub_smaller ha hb hc; ex_middle bad.
by case: (proj2 (ha _ (conj hb bad))).
Qed.

Lemma finite_range f: fgraph f -> finite_set (domain f) ->
  finite_set (range f).
Proof.
move=> /range_smaller => pa pb; apply :(cle_fin_fin pb pa).
Qed.

Lemma finite_image f: function f -> finite_set (source f) -> 
  finite_set (Imf f).
Proof. 
move=> ff fs; move: (image_smaller ff)=> cle.
apply: (cle_fin_fin fs cle).
Qed.

Lemma finite_image_by f A: function f -> 
  finite_set A -> finite_set (Vfs f A).
Proof. 
move=> ff  fsA; move:(image_smaller1 A ff) => cle.
apply: (cle_fin_fin fsA cle).
Qed.

Lemma finite_fun_image a f: finite_set a -> 
  finite_set (fun_image a f).
Proof.
move=> fsa; exact: (cle_fin_fin fsa (fun_image_smaller a f)).
Qed.

Lemma finite_graph_domain f: fgraph f ->
  (finite_set f <-> finite_set (domain f)).
Proof. 
by move=> /Eq_domain /card_eqP; rewrite /finite_set /finite_c => ->.
Qed.


Lemma bijective_if_same_finite_c_inj f: 
  cardinal (source f) = cardinal (target f) -> finite_set (source f) ->
  injection f -> bijection f.
Proof.
move=> csftf fs injf; split=>//; apply: surjective_pr1; first by fct_tac.
have fst: (finite_set (target f)) by hnf; ue. 
have sit: (sub (Imf f) (target f)) by apply: Imf_Starget; fct_tac.
by apply:(strict_sub_smaller_contra fst sit); rewrite (cardinal_range injf).
Qed.

Lemma bijective_if_same_finite_c_surj f: 
  cardinal (source f) = cardinal (target f) -> finite_set (source f) ->
  surjection f -> bijection f.
Proof. 
move=> cstf fsf sf. 
move: (exists_right_inv_from_surj sf)=> [g rig].
move: (right_i_source rig) =>sg. 
move: (right_inverse_fi rig)=> ig.
move: rig =>[co c]; move: (co) => [_ s t].  
have csftf: (cardinal (source g) = cardinal (target g)) by rewrite sg -t.
have fss: finite_set (source g) by hnf; rewrite sg  - cstf.
have bg :=(bijective_if_same_finite_c_inj csftf fss ig).
have bc: (bijection (compose f g)) by rewrite c; apply: identity_fb.
apply: (left_compose_fb co bc bg).
Qed.

(** **  EIII-4-3 The principle of induction *)



Lemma Nat_induction (r:property):
  (r \0c) -> (forall n, natp n -> r n -> r (csucc n)) ->
  (forall n, natp n -> r n).
Proof. 
move=> r0 ri n nN.
case: (p_or_not_p (r n)) => // nrn.
case: (least_int_prop2 nN nrn (p := fun  t => ~ r t)) => //.
by move => [xN nsr /excluded_middle rx]; case: nsr; apply: ri.
Qed.

Lemma Nat_induction_alt (r:property):
  (r \0c) -> (forall n, natp n -> r n -> r (csucc n)) ->
  (forall n, natp n -> r n).
Proof.  
move=> r0 ri. apply:(omega_rec r0) => i iN.
by rewrite - (succ_of_nat iN); apply: ri.
Qed.


Lemma Nat_induction1 (r:property):
  let s:= fun n => forall p, p <c n -> r p in
  (forall n, natp n -> s n -> r n) -> 
  (forall n, natp n -> r n).
Proof. 
(* alternate proof
move=> s si.
suff: forall a, ordinalp a -> ~natp a \/ r a.
  by move => h n nN; case: (h _ (OS_nat nN)).
apply: (least_ordinal2) => b ob oc.
case: (p_or_not_p (natp b))=> bN; [  right; apply:(si _ bN) | by left].
by move => a lab; move: (NS_lt_nat lab bN) (oc _ (oclt lab)) => h; case.
*)
(* alternate proof
move => s h n nN; ex
_middle bad.
move:(least_int_prop (p := fun z => ~r z) nN bad). set y := least_ordinal _ _.
move =>[qa qb qc]. case: qb; apply:h => // i lin; ex_middle bad2.
by case/cleNgt:(qc _ (NS_lt_nat lin  qa) bad2).b *)

move=> s si n nN; apply: (si)=>//.
move: n nN; apply: Nat_induction; first by move=> p /clt0.
move=> m mN sm p lp.
case: (equal_or_not p m); first by move=>->; apply: si =>//. 
by move=> pm; apply: sm=>//; split=>//; apply /(cltSleP mN).
Qed.

(*
Lemma Nat_induction2 (r:property) k:
  natp k -> r k -> 
  (forall n, natp n -> k <=c n -> r n -> r (csucc n)) ->
  (forall n, natp n -> k <=c n -> r n).
Proof. 
move=> fk rk ri n fn kn.
move: n fn kn; apply: Nat_induction; first by move=> h; rewrite - (cle0 h).
move=> m fm sm; case: (equal_or_not k (csucc m)); first by move => <-. 
move => ks ksm. 
move/(cltSleP fm):(conj ksm ks) => lekm. 
by apply: ri=>//; apply: sm.
Qed.
*)

Lemma Nat_induction3 (r:property) a b:
  natp a -> natp b -> r a -> 
  (forall n, a <=c n -> n <c b -> r n -> r (csucc n)) ->
  (forall n, a <=c n  -> n <=c b -> r n).
Proof. 
move=> aN bN ra ri n an nb.
have nN:= NS_le_nat nb bN.
move: n nN an nb; apply: Nat_induction.
   by move =>  az _;  rewrite -(cle0 az).
move=> m mN sm am; move/(cleSltP mN) => mb.
case: (equal_or_not a (csucc m));[ by move => <- | move=> asm]. 
move/(cltSleP mN): (conj am asm) => leam. 
apply: (ri _ leam mb (sm leam (proj1 mb))).
Qed.

Lemma Nat_induction4 (r:property) a b:
  natp a -> natp b ->  r b -> 
  (forall n, a <=c n -> n <c b -> r (csucc n) -> r n) ->  
  (forall n, a <=c n -> n <=c b -> r n).
Proof. 
move=> aN bN rb ti n an nb.  
set (q := fun n => ~ (r n)). 
case: (p_or_not_p (r n))=>// nrn.
have nN:= NS_le_nat nb bN. 
have qi: (forall m, n <=c m -> m <c b -> q m -> q (csucc m)).
  rewrite /q;move=> m nm mb qm; dneg rs; apply: ti=> //; exact: cleT an nm.
by move: ((Nat_induction3 nN bN nrn qi) _ nb (cleR (proj32 nb))).
Qed.

Lemma setU1_finite X x: 
  finite_set X -> finite_set (X +s1 x).
Proof. 
move=>fX; case: (inc_or_not x X) => h; first by rewrite (setU1_eq h).
rewrite/finite_set (csucc_pr h); apply /finite_succP; fprops.
Qed.

Lemma set1_finite x: finite_set(singleton x).
Proof.
apply/ card_finite_setP; rewrite cardinal_set1; apply: NS1.
Qed.

Lemma set2_finite x y: finite_set (doubleton x y).
Proof.
rewrite -(setU2_11 x y); apply: setU1_finite; apply: set1_finite.
Qed.

Lemma finite_set_scdo:  finite_set (substrate canonical_doubleton_order).
Proof.
rewrite (proj2 cdo_wor); apply: set2_finite. 
Qed.

Lemma setU1_succ_card x n: cardinalp n -> cardinal x = csucc n ->
  exists u v, [/\ x = u +s1 v, ~(inc v u) & cardinal u = n].
Proof. 
move=> cn cx.
case: (emptyset_dichot x) => h.
  by case:(@succ_nz n); rewrite - cx h cardinal_set0.
move: h=> [y yx].
have xt:= (setC1_K yx).
exists (x -s1 y), y;split =>//;first by apply: setC1_1. 
apply: csucc_inj; fprops.
by rewrite - cx -xt (csucc_pr1 x y) xt. 
Qed.

Lemma finite_set_induction0  (s:property):
  s emptyset -> (forall a b, s a -> ~(inc b a) -> s (a +s1 b)) ->
  forall x, finite_set x -> s x.
Proof. 
move=> se si x /card_finite_setP cxN.
pose r n :=  forall x, cardinal x = n -> s x. 
have r0: r \0c by  move => y h; rewrite (card_nonempty h).
apply: (Nat_induction r0 _ cxN _ (erefl (cardinal x))) => n nN rn y yp.
move: (setU1_succ_card (CS_nat nN) yp) =>  [u [v [yt nvu cu]]].
by rewrite yt; apply: si=>//; apply: rn.
Qed.

Lemma finite_set_induction (s:property):
  s emptyset -> (forall a b, s a -> s (a +s1 b)) ->
  forall x, finite_set x -> s x.
Proof.  
by move => se si x fs; apply: finite_set_induction0 => // a b sa _; apply: si. 
Qed.

Lemma finite_set_induction1 (A B:property):
  (A emptyset -> B emptyset) ->
  (forall a b, (A a -> B a) -> A(a +s1 b) ->  B(a +s1 b)) ->
  forall x, finite_set x -> A x -> B x.
Proof. exact: (finite_set_induction). Qed.


Lemma finite_set_induction2 (A B:property):
  (forall a, A (singleton a) -> B (singleton a)) ->
  (forall a b, (nonempty a -> A a -> B a) ->  
    nonempty a -> A(a +s1 b) -> B(a +s1 b)) ->
  forall x, finite_set x -> nonempty x -> A x -> B x.
Proof. 
move=> fA fr; apply: finite_set_induction; first by move=> [t /in_set0].
move=> a b sa.
case: (emptyset_dichot a) => pa. 
  have ->: (a +s1 b = singleton b) by rewrite pa; exact: set0_U2.
  by move =>  _; apply: fA.
by move => _;  apply:fr.
Qed.

Lemma csum_via_succ a b: cardinalp b -> a +c (csucc b) = csucc (a +c b).
Proof.
move => cb; rewrite (csucc_pr4 cb) csumA (csucc_pr4) //; fprops.
Qed.

Lemma cprod_via_sum a b: cardinalp b ->  a *c (csucc b) = (a *c b) +c a. 
Proof.
move=> cb; rewrite (csucc_pr4 cb) cprodDr.
rewrite - (csum2cr (a *c b) a) - (cprod1l (CS_cardinal a)).
by rewrite (cprod2cr \1c a) (cprodC \1c).
Qed.

Lemma cpow_succ' a b: cardinalp b -> a ^c (csucc b) = (a ^c b) *c a.
Proof. 
by move=> cb; rewrite (csucc_pr4 cb) cpow_sum2 (cpowx1c a) cprod2cr.
Qed.

Lemma csum_nS a b: natp b -> a +c (csucc b) = csucc (a +c b).
Proof. move => /CS_nat; apply: csum_via_succ. Qed.

Lemma csum_Sn a b: natp a ->  (csucc a) +c b = csucc (a +c b).
Proof. by move=> aN; rewrite csumC (csum_nS _ aN) csumC. Qed.

Lemma cprod_nS a b: natp b -> a *c (csucc b) = (a *c b) +c a. 
Proof. move => /CS_nat; apply: cprod_via_sum. Qed.

Lemma cprod_Sn m n: natp m -> (csucc m) *c n = n +c (m *c n).
Proof. by move => mN; rewrite cprodC (cprod_nS _ mN) csumC cprodC. Qed.

Lemma cpow_succ a b: natp b ->  a ^c (csucc b) = (a ^c b) *c a.
Proof. move => /CS_nat; apply: cpow_succ'. Qed.

Lemma NS_sum a b: natp a -> natp b -> natp (a +c b).
Proof. 
move=> aN bN.
move: b bN; apply: Nat_induction; first by rewrite Nsum0r.
move=> n fn fan; rewrite (csum_nS a fn); fprops.
Qed.

Lemma NS_prod a b: natp a -> natp b -> natp (a *c b).
Proof.
move=> aN bN.
move: b bN; apply: Nat_induction; first by rewrite cprod0r; fprops.
by move=> n nN mN; rewrite cprod_nS; fprops; apply: NS_sum.  
Qed.

Lemma NS_pow a b: natp a -> natp b -> natp (a ^c b).
Proof.
move=> aN bN. 
move: b bN; apply: Nat_induction; first by rewrite cpowx0; fprops.
by move=> n nN mN; rewrite cpow_succ => //;apply: NS_prod.  
Qed.

Lemma NS_pow2 n: natp n -> natp (\2c ^c n).
Proof. apply: NS_pow; fprops. Qed.

Global Hint Resolve NS_sum NS_prod: fprops.
Global Hint Resolve NS_pow NS_pow2: fprops.


Lemma setU2_finite x y:
  finite_set x -> finite_set y -> finite_set (x \cup y).
Proof.
move=> /NatP cxN /NatP cyN; apply /NatP.
move:(csum2_pr6 x y); rewrite - csum2cl - csum2cr => ha.
apply: (NS_le_nat ha (NS_sum cxN cyN)).
Qed.


Lemma finite_prod2 u v: 
   finite_set u -> finite_set v -> finite_set (u \times v).
Proof.
move =>/NatP ha /NatP hb; apply /NatP.
by rewrite - cprod2_pr1 - cprod2cl - cprod2cr; fprops.
Qed.

Lemma cdiff_n0 a: natp a -> a -c \0c = a.
Proof. by move => ca;rewrite /cdiff setC_0 (card_nat ca). Qed.

Lemma cdiff_wrong a b: a <=c b -> a -c b = \0c.
Proof.
by move => [_ _ ab]; rewrite /cdiff (setC_T ab) cardinal_set0.
Qed.

Lemma csum_fin_infin a b: finite_c a -> infinite_c b -> a +c b = b.
Proof.
move/NatP => aN ifb; move: a aN; apply:Nat_induction.
  by rewrite (csum0l  (proj1 ifb)).
move/csucc_inf: ifb => csb.
by move => a aN hr; rewrite (csum_Sn _ aN) hr - csb.
Qed.

Lemma cdiff_fin_infin a b: finite_c a -> infinite_c b ->  b -c a = b.
Proof.
move => ha hb; move: (cdiff_pr (cle_fin_inf ha hb)) => ea.
case: (finite_or_infinite (CS_diff b a)) => fd.
  move: ha fd => /NatP aN /NatP dN; move:(NS_sum aN dN); rewrite ea => /NatP.
  by case/ finite_not_infinite.
by move: ea; rewrite  (csum_fin_infin ha fd).
Qed.

Lemma cdiff_succ a b:
  cardinalp a -> cardinalp b -> (csucc a) -c (csucc b) = a -c b.
Proof.
move => ca cb.
case :(cleT_el ca cb) => lea.
  by move:(cleSS lea) => leb; rewrite (cdiff_wrong leb)(cdiff_wrong lea).
case /finite_or_infinite: cb => fb; last first.
  move:(cle_inf_inf fb (proj1 lea)) => /csucc_inf <-.
  by move/csucc_inf: fb <-.
case /finite_or_infinite: ca => fa; last first.
  move/(finite_succP (proj31_1 lea)):(fb) => fsb.
  move /csucc_inf: (fa) => <-.
  by rewrite (cdiff_fin_infin fsb fa)(cdiff_fin_infin fb fa).
move: fa fb => /NatP aN /NatP bN.
rewrite (succ_of_nat aN) (succ_of_nat bN) /cdiff /osucc.
move/olt_i: (oclt lea) => iba.
move:(oclt lea) => [[ob oa sab] anb].
have aa:= (ordinal_irreflexive oa).
set E :=  (a -s (b +s1 b)).
have naE: ~inc a E by move /setC_P => [/aa].
have nbE: ~inc b E by move /setC_P => [_] /setU1_P; case; right.
have -> : a -s b = E +s1 b.
  set_extens t.
    move/setC_P => [ta tb];case: (equal_or_not t b) => tc.
      by rewrite tc; fprops.
    by apply:setU1_r; apply: (setC_i ta);case/setU1_P.
  case/setU1_P.
    move/setC_P => [ta ntb];apply: (setC_i ta) => itb; case: ntb; fprops.
  move => ->; apply: (setC_i iba); apply:(ordinal_irreflexive ob).
have -> : ((a +s1 a) -s (b +s1 b)) = E +s1 a.
  set_extens t.
    move/setC_P => [ta tb]; case/setU1_P: ta => ta.
      by apply:setU1_r;apply/setC_P.
    by rewrite ta; apply:setU1_1.
  case/setU1_P.
    move/setC_P => [ta tb]; apply:(setC_i _ tb); fprops.
  move ->; apply/setC_P; split => //; fprops => w.
  by move: (extensionality sab (ordinal_sub3 ob w)). 
by rewrite (csucc_pr naE) (csucc_pr nbE).
Qed.

Lemma cdiff_pr1' a b: cardinalp a -> natp b -> (a +c b) -c b  = a.
Proof.
move=> aN bN.
have aa: a -c \0c = a by rewrite /cdiff setC_0 (card_card aN).
move: b bN; apply:Nat_induction; first by rewrite (csum0r aN) aa.
by move => n nN hr; rewrite (csum_nS _ nN) (cdiff_succ (CS_sum2 a n) (CS_nat nN)).
Qed.

Lemma cdiff_pr1 a b: natp a -> natp b -> (a +c b) -c b  = a.
Proof. by move=> /CS_nat aN bN; apply: cdiff_pr1'. Qed.


(** **  EIII-4-4 Finite subsets of ordered sets *)

Lemma finite_set_induction3 (p: Set -> Set -> Prop) E:
  (forall a b, inc a E -> inc b E -> exists y, p (doubleton a b) y) ->
  (forall a b x y, sub a E -> inc b E -> p a x -> p (doubleton x b) y->
    p (a +s1 b) y) ->
  (forall X x, sub X E -> nonempty X -> p X x -> inc x E) ->
  forall X, finite_set X -> nonempty X -> sub X E -> exists x, p X x.
Proof. 
move=> p1 p2 p3.
apply: finite_set_induction2.
  move=> a aE; have ae:= (aE _ (set1_1 a)).
  exact:(p1 a a ae ae).
move=> a b p4 nea st.
have saE: sub a E by apply: sub_trans st; fprops.
have bE: inc b E by apply: st;fprops.
have [y py] := (p4 nea saE).
have yE:=  (p3 _ _ saE nea py).
have [z pz] := (p1 _ _ yE bE).
exists z; apply: p2 saE bE py pz.
Qed. 

Lemma finite_subset_directed_bounded r X:
  right_directed r -> finite_set X -> nonempty X -> sub X (substrate r) -> 
  bounded_above r X.
Proof. 
move=> [or rr].
apply: finite_set_induction3 => //; last by move => Y x Ysr neY [sr uYx].
move=> a b x y asr bsr [xsr ubx] [yser upy].
split =>//.
have xy := (upy _ (set2_1 x b)).
have lyb:= (upy _ (set2_2 x b)).
move=> t /setU1_P; case; last by move=>->. 
move => ta; move: (ubx _ ta)=> aux; order_tac. 
Qed.

Lemma finite_subset_lattice_inf r X:
  lattice r -> finite_set X ->  nonempty X -> sub X (substrate r) ->
  exists x, greatest_lower_bound r X x.
Proof. 
move=> [or lr];apply: finite_set_induction3.
+ by move=>a b asr bsr; move: (lr _ _ asr bsr)=> [p1 p2].
+ move=> a b x y asr bsr.
  move /(glbP  or asr)=> [[xsr lb] glex].
  have st: sub (a +s1 b) (substrate r) by apply: setU1_sub.
  have sd: sub (doubleton x b) (substrate r) by apply: sub_set2.
  move=> /(glbP or sd)  [[ysr lby] lgley].
  have xy := (lby _ (set2_1 x b)).
  have lbyy:= (lby _ (set2_2 x b)).
  apply /(glbP or st); split.
    split =>// z /setU1_P; case; last by move=> ->.
    move=>za; move: (lb _ za)=> xa; order_tac.
  move=> z [ze xx].
  apply: lgley; split=>//; move=> t /set2_P [] ->.
    apply: glex; split=>//.
    move=> u ua; apply: xx; fprops.
  apply: xx; fprops.
+ by move=> Z x Zr _ /(glbP or Zr) [[xsr _] _]. 
Qed.

Lemma finite_subset_lattice_sup r X:
  lattice r -> finite_set X -> nonempty X -> sub X (substrate r) -> 
  exists x, least_upper_bound r X x.
Proof. 
move=> [or lr];apply: finite_set_induction3. 
+ by move=>a b asr bsr;  move: (lr _ _ asr bsr)=> [p1 p2].
+ move=> a b x y asr bsr.
  move /(lubP  or asr)=> [[xsr lb] glex].
  have st: sub (a +s1 b) (substrate r) by apply: setU1_sub.
  have sd: sub (doubleton x b) (substrate r) by apply: sub_set2.
  move=> /(lubP or sd)  [[ysr lby] lgley].
  have xy:= (lby _ (set2_1 x b)). 
  have lbyy := (lby _ (set2_2 x b)).
  apply /(lubP or st); split.
    split =>// z /setU1_P; case; last by move=> ->.
    move=>za; move:  (lb _ za)=> xa; order_tac.
  move=> z [ze xx].
  apply: lgley; split=>//; move=> t /set2_P [] ->.
    apply: glex; split=>//.
    move=> u ua; apply: xx; fprops.
  apply: xx; fprops.
by move=> Z x Zr _ /(lubP or Zr) [[xsr _] _]. 
Qed.

Lemma finite_subset_torder_greatest r X:
  total_order r -> finite_set X -> nonempty X -> sub X (substrate r) -> 
  has_greatest (induced_order r X).
Proof. 
move=> [or tor].
move: X;apply: finite_set_induction3.
+ move=> a b asr bsr.
    have sd: sub (doubleton a b) (substrate r) by apply: sub_set2.
    have aux:  (substrate (induced_order r (doubleton a b))) = doubleton a b.
      by rewrite iorder_sr.
    by case: (tor _ _ asr bsr)=> cp; [exists b | exists a]; hnf;rewrite aux;
       split; fprops; move=> x /set2_P [] ->; apply/iorder_gle0P; 
       fprops; order_tac.
+ move=> a b x y asr bsr;rewrite /greatest.
  have sta: (sub (a +s1 b) (substrate r)) by apply: setU1_sub. 
  rewrite iorder_sr //;  move=> [xa xp].
  have xsr := (asr _ xa).
  have sd: sub (doubleton x b) (substrate r) by apply: sub_set2.
  move: xp; rewrite iorder_sr //; move=>  xp [yd yp]. 
  rewrite iorder_sr //;split.
    move: yd => /set2_P []->; fprops.
  have xy:= (iorder_gle1 (yp _ (set2_1 x b))).
  have lby:= (iorder_gle1 (yp _ (set2_2 x b))).
  have yt: inc y (a +s1 b) by case /set2_P: yd => ->; fprops.
  move=> z zi; apply /iorder_gle0P => //.
  case /setU1_P: zi => h; last by ue.
  have zx:=(iorder_gle1 (xp _  h)) ; order_tac. 
+ move=> Z x Zs neZ [h gex]; apply: (Zs).
  by move: h; rewrite iorder_sr.
Qed.

Lemma finite_subset_torder_least r X:
  total_order r -> finite_set X -> nonempty X -> sub X (substrate r) -> 
  has_least (induced_order r X).
Proof. 
move=> tor fsX neX Xsr.
have or: order r by move: tor=> [].
have rtor:=(total_order_opposite tor).
move: (opp_osr or) => [aa so]; move: (Xsr); rewrite - so => rXsr. 
move: (finite_subset_torder_greatest rtor fsX neX rXsr)=> [x []].
rewrite iorder_sr // => xX xg.
exists x; hnf;rewrite iorder_sr//;split => //.
move=>  a aX; move: (iorder_gle1 (xg _ aX)) => /igraph_pP h.
by apply /iorder_gleP.
Qed.

Lemma finite_set_torder_greatest r:
  total_order r -> finite_set (substrate r) -> nonempty (substrate r) ->
  has_greatest r.
Proof. 
move=> tor fss nes; move: (tor)=> [or _].
rewrite - (iorder_substrate or). 
apply: finite_subset_torder_greatest; fprops.
Qed.

Lemma finite_set_torder_least r:
  total_order r -> finite_set (substrate r) -> nonempty (substrate r)  ->
  has_least r.
Proof. 
move=> tor fss nes; move: (tor)=> [or _].
rewrite - (iorder_substrate or). 
apply: finite_subset_torder_least; fprops.
Qed.

Lemma finite_set_torder_wor r:
  total_order r -> finite_set (substrate r) -> worder r.
Proof. 
move=> tor fse; move: (tor)=> [or _].
split=>//  z zs zne.
apply: finite_subset_torder_least =>//.
apply: (sub_finite_set zs fse).
Qed.


Lemma finite_subset_Nat X: sub X Nat -> finite_set X -> nonempty X ->
   exists2 n, inc n X & forall m, inc m X -> m <=c n.
Proof.
move => pa pb pc.
move: (wordering_cle_pr CS_nat) => [wor sr].
have pd: sub X (substrate (graph_on cardinal_le Nat))  by rewrite sr.
move: (finite_subset_torder_greatest (worder_total wor) pb pc pd).
move => [n []]; rewrite (iorder_sr (proj1 wor) pd) => pe pf; ex_tac.
by move => m /pf /iorder_gle1/graph_on_P0/proj33.
Qed.

  
Lemma Nat_sup_pr T (s:= \csup T) k: 
  natp k -> (forall i, inc i T -> i <=c k) ->
  [/\ natp s, s <=c k,
    (forall i, inc i T -> i <=c s) &
    (T = emptyset \/ inc s T)].
Proof.
move=> kN km.
case: (emptyset_dichot T) => Tne.
  rewrite /s Tne setU_0; split; fprops.
    by apply: cle0n.    
  by move => i /in_set0.
have pa: sub T (csucc k) by move => t /km /(NleP kN).
have TN: sub T Nat by move => t /km h; apply:(NS_le_nat  h kN).
have fsT: finite_set T.
  apply:(sub_finite_set pa); apply: finite_set_nat; fprops.
move: (@finite_subset_Nat T TN fsT Tne) => [n nT nm].
have pb: cardinal_set  T by move => t /TN/CS_nat.
have nN := TN _ nT.
move: (cleA (card_ub_sup (CS_nat nN) nm) (card_sup_ub pb nT)) => eq.
rewrite /s eq; split => //; [ by apply: km | by right ].
Qed.

Lemma finite_set_maximal r:
  order r -> finite_set (substrate r) -> nonempty (substrate r) ->
  exists x, maximal r x.
Proof.
move=> or fse nes; apply: Zorn_lemma=>//. 
move => X Xsr toX.
case: (emptyset_dichot X)=> xe.  
  rewrite xe;move: nes=> [z zE]; exists z; split=>//; move=> y; case; case. 
set (s:= induced_order r X) in toX. 
have sr: (substrate s = X) by rewrite iorder_sr.
have fs: (finite_set (substrate s)). 
   by rewrite sr; apply: (sub_finite_set Xsr fse).
have nse: (nonempty (substrate s)) by rewrite sr.
move: (finite_set_torder_greatest toX fs nse)=> [x [xsr xge]]. 
rewrite - sr in Xsr.
rewrite - sr; exists x; split; first by apply: Xsr.
move=> y yX; exact (iorder_gle1 (xge _ yX)).
Qed.


Lemma finite_set_minimal r:
  order r -> finite_set (substrate r) -> nonempty (substrate r) ->
  exists x, minimal r x.
Proof.
move => or.
move: (opp_osr or) => [or' sr'].
rewrite - sr' => fsr nes.
move: (finite_set_maximal or' fsr nes) => [x xf]; exists x.
by apply /maximal_opp.
Qed.

Section LatticeProps.

Variable (r: Set).
Hypothesis lr: lattice r.
Let E := substrate r.

Lemma lattice_finite_sup2 x:
  finite_set x ->  nonempty x ->  sub x E -> has_supremum r x.
Proof. 
move:x;  apply: (finite_set_induction2).
  move => a asr;rewrite -/(singleton a).
  have ar: inc a (substrate r) by apply: asr; fprops.
  by move: lr => [or lr1]; move: (lr1 _ _ ar ar) =>[p1 p2].
move=> a b Hr nea ss. 
have p1: sub a (substrate r) by apply: sub_trans ss; fprops.
have p2: inc b (substrate r) by apply: ss; fprops.
have [c cs] := (Hr nea p1).
exists (sup r c b);apply: (lattice_finite_sup1 lr p1 cs p2).
Qed.
  
Lemma lattice_finite_inf2 x:
  finite_set x ->  nonempty x -> sub x E -> has_infimum r x.
Proof. 
move:x;apply: finite_set_induction2. 
  move => a asr;rewrite -/(singleton a).
  have ar: inc a (substrate r) by apply: asr; fprops.
  by move: lr => [or lr1]; move: (lr1 _ _ ar ar) =>[p1 p2].
move=> a b Hr nea ss.
have p1: sub a (substrate r) by apply: sub_trans ss; fprops.
have p2: inc b (substrate r) by apply: ss; fprops.
have [c cs]:= (Hr nea p1).
exists (inf r c b); apply: (lattice_finite_inf1 lr p1 cs p2).
Qed.

Lemma lattice_finite_sup3P x y:
  finite_set x -> nonempty x -> sub x E -> 
  (gle r (supremum r x) y <-> (forall z, inc z x -> gle r z y)).
Proof. 
move=> fsx nex xsr.
have hs:= (lattice_finite_sup2 fsx nex xsr).
have or: order r by case:lr. 
move: (supremum_pr or xsr hs) => [[p1 p2] p3]; split. 
  move=> p4 z zx; move: (p2 _ zx) => p5; order_tac.
move=> p4; apply: p3; split => //.
move: nex=> [u ux]; move: (p4 _ ux) => p5; order_tac.
Qed.

Lemma lattice_finite_inf3P  x y:
  finite_set x -> nonempty x -> sub x E -> 
  (gle r y (infimum r x) <-> (forall z, inc z x -> gle r y z)).
Proof.
move=> fsx nex xsr.
have hs:= (lattice_finite_inf2 fsx nex xsr).
have or: order r by move: lr => [ok _]. 
have [[p1 p2] p3] := (infimum_pr or xsr hs). 
split; first by move=> p4 z zx; move: (p2 _ zx) => p5; order_tac.
move=> p4; apply: p3; split => //.
move: nex=> [u ux]; move: (p4 _ ux) => p5; order_tac.
Qed.

Lemma supremum_setU1 a b:
  sub a E -> has_supremum r a -> inc b E ->
  supremum r (a +s1 b) =  sup r (supremum r a) b.
Proof.
move=> asr hsa bsr; move: lr => [or _]; symmetry; apply: supremum_pr2 =>//.
by apply: lattice_finite_sup1 => //;apply: supremum_pr1.
Qed.

Lemma infimum_setU1 a b:
  sub a E -> has_infimum r a -> inc b E ->
  infimum r (a +s1 b) =  inf r (infimum r a) b.
Proof.
move: lr => [or _]; move=> asr hsa bsr; symmetry; apply: infimum_pr2 => //.
by apply: lattice_finite_inf1 => //;apply: infimum_pr1.
Qed.

Lemma sup_setU1 X a:
   sub X E -> nonempty X -> finite_set X ->
   inc a E -> supremum r (X +s1 a) = sup r (supremum r X) a.
Proof.
move => pb pc pd pe; apply:supremum_setU1 => //.
by apply: lattice_finite_sup2.
Qed.

Lemma inf_setU1 X a:
   sub X E -> nonempty X -> finite_set X ->
   inc a E -> infimum r (X +s1 a) = inf r (infimum r X) a.
Proof.
move => pb pc pd pe; apply:infimum_setU1 => //.
by apply: lattice_finite_inf2.
Qed.

End LatticeProps.

(** **  EIII-4-5  Properties of finite character *)

Definition finite_character s:=
  forall x, (inc x s) <-> (forall y, (sub y x /\ finite_set y) -> inc y s).

Lemma finite_character_example r: order r ->
  finite_character(Zo (\Po (substrate r)) (fun z =>
    total_order (induced_order r z))).
Proof.
move=> or s; split.
  move /Zo_P => [] /setP_P sr tor y [ys fsy];apply: Zo_i.
     have sys: (sub y (substrate r)) by apply: sub_trans sr. 
     by apply /setP_P.
  have ->: (induced_order r y) =  (induced_order  (induced_order r s) y).
    by rewrite  iorder_trans.
  apply: total_order_sub =>//; rewrite iorder_sr//.
move=> h.
have p1: sub s (substrate r).
  move=> t ts; set (y:= singleton t).
  have p1: (sub y s) by rewrite/y; apply: set1_sub.
  have p2: (finite_set y) by rewrite /y; apply: set1_finite. 
  have p3: (sub y s /\ finite_set y) by split => //.
  move: (h _ p3) => /Zo_P [] /setP_P ysr _.
  apply: ysr; rewrite /y; fprops.
apply: Zo_i; first by apply /setP_P.
move: (iorder_osr or p1) => [pa pb].
split => //; rewrite pb.
move=> x y xs ys; rewrite /ocomparable.
set (z:= doubleton x y). 
have p2: (sub z s /\ finite_set z).
  by split; rewrite /z; [ apply: sub_set2 |apply: set2_finite]. 
move:  (h _ p2) => /Zo_P [] /setP_P zsr [oz]; rewrite iorder_sr // => toz.
case: (toz _ _ (set2_1 x y) (set2_2 x y)) => h1; [left | right];
   apply /iorder_gle0P => //; exact: (iorder_gle1 h1).
Qed.

Lemma maximal_inclusion s: finite_character s -> nonempty s ->
  exists x, maximal (sub_order s) x.
Proof. 
move=>fs nes.
have es: inc emptyset s.
  move: nes=> [x]; rewrite fs=> aux; apply: aux.
  split; [ fprops | apply: emptyset_finite].
set (E:=union s). 
  have sp: (sub s (\Po E)) by move=> t ts; apply /setP_P; apply: setU_s1.
apply: (setP_maximal(A:=s) (F:=E)) =>//.
move=> u tou us.
rewrite fs; move=> y [ysu fsy].
case: (emptyset_dichot y) => yne; try ue. 
set(Zy:= fun a => choose (fun b=> inc a b /\ inc b u)).
have Zyp: (forall a, inc a y -> (inc a (Zy a) /\ inc (Zy a) u)). 
  move=> a ay; rewrite /Zy; apply choose_pr.  
  by move: (ysu _ ay)=> aux; move: (setU_hi aux) => [v pa pb]; exists v.
set (Zz:= fun_image y Zy).
have fsZz: (finite_set Zz) by rewrite /Zz; apply: finite_fun_image. 
move: (sub_osr Zz) => []; set r:=(sub_order Zz) => pa pb.
have tor: (total_order r). 
  split => //; rewrite pb /r /ocomparable;move=> a b aZz bZz.
  have au: (inc a u) by move: aZz => /funI_P [z /Zyp [_ zy] ->]. 
  have bu: (inc b u) by move: bZz => /funI_P [z /Zyp [_ zy] ->]. 
  case: (tou _ _ au bu) =>h; [left | right]; apply /ordo_leP;split => //.
have fsr: (finite_set (substrate r)) by ue.
have ner: nonempty (substrate r). 
  move: yne=> [w wy]; exists (Zy w) ; rewrite pb; apply /funI_P; ex_tac.
move: (finite_set_torder_greatest tor fsr ner) => [x [xsr xgr]].
have ysr: (sub y x). 
  move => t ty.
  have aux: (inc (Zy t)(substrate r)) by rewrite pb; apply /funI_P; ex_tac.
  move /ordo_leP: (xgr _ aux).
  move: (Zyp _ ty)=> [tZ _] [_ _ Zx]; apply: Zx =>//.
rewrite fs; move=> z [zy fsz]; move: (sub_trans zy ysr) => zx.
move: xsr; rewrite pb; move /funI_P=> [w wy Zyw]. 
move: (Zyp _ wy); rewrite - Zyw; move => [_ xu].
by move: (us _ xu); rewrite fs; apply. 
Qed.

Lemma maximal_inclusion_aux: let s := emptyset in
  finite_character s /\ 
  ~ (exists x, maximal (sub_order s) x).
Proof.
split.
   move=> x; split; first by move => /in_set0.
   move=> h; have: (inc emptyset emptyset).
     apply: h;split; [ fprops | apply: emptyset_finite].
   by move /in_set0.
by move=> [x [xe _]]; move: xe;rewrite (proj2 (sub_osr _))=> /in_set0. 
Qed.

Fixpoint nat_to_B (n:nat) :=
  if n is m.+1 then csucc (nat_to_B m) else  \0c.

Lemma nat_to_B_succ n:
  csucc (nat_to_B n) = (nat_to_B n.+1).
Proof. by done. Qed.

Lemma nat_to_B_Nat n: natp (nat_to_B n).
Proof. 
elim :n; first by simpl; fprops.
by move=> n nN /=; apply: NS_succ.
Qed.

Lemma nat_to_B_injective: injective nat_to_B.
Proof.
elim.
  elim => // n h /= es; move: (@succ_nz (nat_to_B n)); rewrite -es //.
move => n h; elim => [/= es | m h1 /= aux].
  by move: (@succ_nz (nat_to_B n)); rewrite es.
have cn := (CS_nat (nat_to_B_Nat n)).
have cm:= (CS_nat (nat_to_B_Nat m)).
congr (_ .+1); apply: h;exact: (csucc_inj cn cm aux).
Qed.

Lemma nat_to_B_surjective x: natp x -> exists n, x = nat_to_B n.
Proof.
move: x; apply: Nat_induction.
  by exists 0.
by move=> n nN [m mv]; exists m.+1 ; rewrite mv //.
Qed.


(* Inverse function of nat_to_B via the axiom of choice *)
Fact nonempty_nat: inhabited nat.
Proof. exact (inhabits 0). Qed.

Definition B_to_nat x :=  (chooseT (fun y => x = nat_to_B y) nonempty_nat).


Lemma B_to_nat_pa x: natp x -> (nat_to_B (B_to_nat x)) = x.
Proof.
move => H; symmetry.
apply:(chooseT_pr nonempty_nat (nat_to_B_surjective H)). 
Qed.

Lemma B_to_nat_pb p : B_to_nat (nat_to_B p) = p.
Proof. exact: (nat_to_B_injective (B_to_nat_pa (nat_to_B_Nat p))). Qed.


Lemma nat_to_B_sum x y: nat_to_B (x + y) = nat_to_B x +c nat_to_B y.
Proof.
elim: y => [|n hrec /=].
   rewrite addn0 csum0r //; exact (CS_nat (nat_to_B_Nat x)).
by rewrite  (csum_nS _ (nat_to_B_Nat n)) addnS - hrec.
Qed.

Lemma nat_to_B_prod x y: nat_to_B (x * y) = nat_to_B x *c nat_to_B y.
Proof.
elim: y =>[| n hrec /=]; first by rewrite muln0 cprod0r. 
by rewrite (cprod_nS _ (nat_to_B_Nat n)) mulnS nat_to_B_sum hrec csumC.
Qed.

Lemma nat_to_B_pow x y: nat_to_B (x ^ y) = nat_to_B x ^c nat_to_B y.
Proof.
elim: y =>[| n hrec /=]; first by  rewrite cpowx0 //=; exact succ_zero.
by rewrite (cpow_succ _ (nat_to_B_Nat n)) expnS nat_to_B_prod hrec cprodC.
Qed.

Lemma nat_to_B_le x y: x <=y <-> nat_to_B x <=c nat_to_B y.
Proof.
split.
  move /subnKC => h; move: (nat_to_B_sum x (y - x)); rewrite h => ->.
  apply: csum_M0le; apply: CS_nat; apply: nat_to_B_Nat.
move/cdiff_pr.
set z := (nat_to_B y -c nat_to_B x).
have zb: natp z by apply: NS_diff; apply: nat_to_B_Nat.
have [u ->]:= (nat_to_B_surjective zb).
rewrite - nat_to_B_sum => /nat_to_B_injective <-.
apply:leq_addr.
Qed.


Lemma nat_to_B_lt x y: x < y <-> nat_to_B x <c nat_to_B y.
Proof.
case:y; first by split => // /clt0.
move => y; rewrite ltnS /=; apply: (iff_trans ( nat_to_B_le x y)).
apply:iff_sym;apply:(cltSleP (nat_to_B_Nat y)).
Qed.



Lemma nat_to_B_diff x y: nat_to_B (x - y) = nat_to_B x -c nat_to_B y.
Proof.
case: (ltnP x y) => p1.
  move: (ltnW p1) => p2. 
  have -> /= : x -y = 0 by apply /eqP.
  rewrite /cdiff.
  by move / nat_to_B_le : p2 => [_ _ /setC_T ->]; rewrite cardinal_set0.
rewrite - {2}(subnK p1) nat_to_B_sum cdiff_pr1 //; apply:nat_to_B_Nat.
Qed.


Lemma nat_to_B_max a b:
   nat_to_B (maxn a b) = cmax (nat_to_B a) (nat_to_B b).
Proof.
case /orP: (leq_total a b) => lab;move/nat_to_B_le: (lab) => lac.
  by rewrite (cmax_xy lac); move/maxn_idPr: lab => ->.
by rewrite (cmax_yx lac); move/maxn_idPl: lab => ->.
Qed.


Lemma nat_to_B_min a b:
   nat_to_B (minn a b) = cmin (nat_to_B a) (nat_to_B b).
Proof.
case /orP: (leq_total a b) => lab;move/nat_to_B_le: (lab) => lac.
  by rewrite (cmin_xy lac); move/minn_idPl: lab => ->.
by rewrite (cmin_yx lac); move/minn_idPr: lab => ->.
Qed.

Lemma nat_to_B_pos n: 0 <n <-> \0c <c nat_to_B n.
Proof. exact: nat_to_B_lt. Qed.

Lemma nat_to_B_gt1 n: 1 <n <-> \1c <c nat_to_B n.
Proof. rewrite - succ_zero -/(nat_to_B 1);  exact: nat_to_B_lt. Qed.

Lemma nat_to_B_ifeq a b u v: let N := nat_to_B in 
  N (if a == b then u else v) = Yo (N a = N b)(N u)(N v).
Proof.           
case: ifP => ab; first by rewrite(eqP ab) /=(Y_true (erefl _)).
by rewrite /= Y_false // =>/nat_to_B_injective xab; move: ab; rewrite xab eqxx.
Qed.
  
Lemma nat_to_B_ifle a b u v: let N := nat_to_B in 
  N (if a <= b then u else v) = Yo (N a <=c N b)(N u)(N v).
Proof.           
simpl;case: (ltnP b a); last by move/nat_to_B_le => ea; Ytac0.
by move/nat_to_B_lt /cltNge => ea; rewrite (Y_false ea).
Qed.

Lemma z_infinite_nat: z_infinite (IM nat_to_B).
Proof.
split; first by apply/IM_P; exists 0.
move => x /IM_P [n ->]; apply/IM_P; exists n.+1.
by rewrite /= (succ_of_nat (nat_to_B_Nat n)). 
Qed.

Lemma z_infinite_nat2: z_infinite Nat.
Proof.
split; first exact: NS0.
by move => n nN; rewrite - (succ_of_nat nN); apply:NS_succ.
Qed. 


Lemma z_infinite_nat3 X: z_infinite X -> sub Nat X.
Proof.
move=> [h1 h2]; apply: Nat_induction => // n nN nx.
by rewrite (succ_of_nat nN); apply: h2.
Qed.

Lemma z_infinite_I X: z_infinite X -> z_omega X = Nat. 
Proof.
move => ha.
move: (z_omega_prop ha) => [qa qb].
apply: extensionality; last by apply: (z_infinite_nat3 qa).
apply: (qb _ z_infinite_nat2).
Qed.

(** Canonical ordering of pairs of ordinals *)

Definition ordinal_pair x := 
  [/\ pairp x, ordinalp (P x) & ordinalp (Q x)].
Definition ord_pair_max x := omax (P x) (Q x).
Definition ord_pair_le  x y:=
   [/\ ordinal_pair x, ordinal_pair y &
   (ord_pair_max x <o ord_pair_max y
    \/ (ord_pair_max x = ord_pair_max y
        /\ ((P x) <o (P y) 
           \/ (P x = P y /\ Q x <=o Q y))))].

Lemma ordering_pair1 x: ordinal_pair x -> 
   ((P x <=o Q x) /\ ord_pair_max x = Q x)
   \/ ((Q x <=o P x) /\ ord_pair_max x = P x).
Proof.
move=> [px op oq]; case:(oleT_ee op oq)=> h ; [left | right ]; split => //.   
  by apply: omax_xy.
by apply: omax_yx.
Qed.

Lemma ordering_pair2 x: ordinal_pair x -> ordinalp (ord_pair_max x).
Proof.
by  move=> h; case: (ordering_pair1 h) => [][[ ha hb _] pb]; rewrite pb.
Qed.

Lemma ordering_pair3 x y : ord_pair_le x y ->
  inc x (coarse (osucc (ord_pair_max y))).
Proof.
move=> [px py le]; apply /setX_P.
move: (ordering_pair2 py) => oo; move: (OS_succ oo) => soo.
set t := (osucc (ord_pair_max y)).
suff: inc (P x) t /\ inc (Q x) t by  move =>[pa pb];split=> //;case:px. 
case: le => [][le aux].
  case: (ordering_pair1 px); move => [pa pb]; rewrite pb in le;
    split;apply /(oltP soo); apply /oltSleP => //; apply:(oleT pa le).
case: (ordering_pair1 px); move=> [pa pb];
  split;apply /(oltP soo); apply /oltSleP => //;
    rewrite -le pb => //;apply:(oleR (proj32 pa)).
Qed.

Lemma ordering_pair4 x: ordinal_pair x -> ord_pair_le x x.
Proof.
move => op; hnf; split => //;  right; split => //; right; split => //.
by move:op => [_ _ ok]; apply: oleR.
Qed.

Lemma well_ordering_pair: worder_r ord_pair_le.
Proof.
move: ordering_pair4  => or1.
have oR: reflexive_rr ord_pair_le.
  by move => x y [p1 p2 _]; split; apply: or1.
have oA: antisymmetric_r ord_pair_le.
  move => x y  [p1 p2 p3] [_ _ q3]; case: p3 => p3; case: q3 => q3.
  + by move: q3 => [q3 _]; case: (oltNge p3 q3).
  + by move: q3 => [q3 _]; rewrite q3 in p3; case: p3. 
  + by move: p3 => [p3 _]; rewrite p3 in q3; case: q3.
  + move: p3 => [p31 p32]; move: q3 => [q31 q32].
    case: p32 => p32; case: q32 => q32.
    - by move: q32 => [q32 _];case: (oltNge p32 q32).
    - by move: q32 => [q32 _]; rewrite q32 in p32; case: p32. 
    - by move: p32 => [p32 _]; rewrite p32 in q32; case: q32.
    - move: p32 => [pa pb]; move: q32 => [_ pc].
      move: p1 p2 => [px _ _][py _ _]; apply: pair_exten => //. 
      by apply:oleA pb pc.
split.
  split => //.
  move => a b c  [p1 p2 p3] [q1 q2 q3]. 
  split ; [exact |  exact | ].
  case: p3 => p3; case: q3 =>  q3.
  - by left; apply: (olt_ltT p3 q3).
  -  move: q3 => [q3a q3b];case: q3b => q3b; first by rewrite q3a in p3; left.
     move: q3b => [q4 q5]; left;ue.
  - by move: p3 => [p31 p32]; rewrite -p31 in  q3; left.
  - move: p3 q3 => [p3 p4] [q3 q4]; right; split => //; first by ue.
    case:p4=> p4.
      left; case: q4; move => [q4 q5]; [ apply:olt_leT p4 q4 |ue ].
    move: p4 => [ -> p4]. 
    case: q4; [by left| move=> [p5 p6];right;split => //;apply:oleT p4 p6].
move => x cx [x0 x0x].
set S1:= fun_image x ord_pair_max.
have os1: ordinal_set S1.
  by move=> t /funI_P [z zx ->]; apply:ordering_pair2; move/cx: zx => []. 
have nes1: nonempty S1 by exists (ord_pair_max x0); apply /funI_P; ex_tac.
move: (ordinal_setI nes1 os1); set gamma:= intersection S1 => gs1.
have g1: forall z, inc z x -> gamma <=o (ord_pair_max z).
  move => z zx.
  have aa: inc (ord_pair_max z) S1 by apply /funI_P; ex_tac.
  move: (os1 _ aa) => ou; split => //. 
     by apply os1.
  by apply: setI_s1.
move: gs1 => /funI_P [g0 g0x g0v].
set S2:= fun_image (Zo x (fun z => ord_pair_max z = gamma)) P.
have nes2: nonempty S2.
   by apply: funI_setne; exists g0 => //; apply: Zo_i.
have os2: ordinal_set S2.
  move =>t /funI_P [z /Zo_S zx ->]. 
  by move: (cx _ zx) => [[ _ aa _] _ _]. 
move: (ordinal_setI nes2 os2); set alpha:= intersection S2 => as1.
have a1: forall z, inc z x ->  gamma <o (ord_pair_max z)
     \/ (gamma = ord_pair_max z) /\ alpha <=o P z.
  move=> z zx; move: (g1 _ zx) => le1.
  case: (equal_or_not gamma (ord_pair_max z)) => eq; last by left.
  have pa: inc (P z) S2 by apply/funI_P; exists z => //; apply: Zo_i => //.
  by right;split => //; hnf; split; fprops;apply: setI_s1.
move: as1 => /funI_P [a0 /Zo_P [a0x ba] qa].
set S3 := fun_image 
   (Zo x (fun z => (ord_pair_max z) = gamma /\ (P z) = alpha)) Q.
have neS3: nonempty S3. 
 by apply: funI_setne; exists a0 => //; apply: Zo_i. 
have os3: ordinal_set S3.
  move =>t /funI_P [z /Zo_P [pa _] ->].
  by move: (cx _ pa) => [[_ qb qc] _].
move: (ordinal_setI neS3 os3); set beta:= intersection S3 => as2.
move: as2 => /funI_P [b0 /Zo_P [b0x [pd pb]] pc].
exists b0; hnf.
rewrite (graph_on_sr cx); split => //.
move=> t tx; apply /graph_on_P1;split => //;split => //.
  by move: (cx _ b0x) => [ok _].
  by move: (cx  _ tx) => [ok _].
case: (a1 _ tx); first by rewrite pd => h; left.
rewrite pd; move=> [pe pf]; right; split => //.
rewrite pb; case: (equal_or_not alpha (P t)) => eq1; last by left.
right; split => //; hnf; split => //.
  by move: (cx _ b0x) => [[_ _ ra] _].
  by move: (cx _ tx) => [[_ _ ra] _].
have pg: inc (Q t) S3 by apply/funI_P; exists t => //; apply: Zo_i => //.
rewrite - pc; apply (setI_s1 pg).
Qed.


Lemma infinite_product_aux k
  (lo:= graph_on ord_pair_le (coarse k))
  (f := ordinal_iso lo):
  infinite_c k ->
  (forall z,  infinite_c z -> z <o k -> z *c z = z) ->
  bijection_prop f (coarse k) k /\
     (forall x y, inc x (source f) -> inc y (source f) ->
       (glt lo x y <-> (Vf f x) <o (Vf f y))).
Proof.
move => ik hrec.
move: (ik) => [[ok _] _]; move: (ik) => [ck _].
have pa: (forall a, inc a (coarse k) -> ord_pair_le a a).
   move => a /setX_P [pa p1a p2a]; apply: ordering_pair4; hnf;split => //.
     apply: (Os_ordinal ok p1a).
   apply: (Os_ordinal ok p2a).
move: (wordering_pr well_ordering_pair pa); rewrite -/lo; move=> [los low].
move: (OS_ordinal los) =>  ot.
move:(ordinal_isomorphism_exists los); rewrite -/f =>  oisf.
move: (oisf) => [or1 or2 [bf sf tf] isf].
rewrite (ordinal_o_sr (ordinal lo)) in tf.
move: (bf) => [injf [ff sjf]].
have fp1: forall a, inc a (source f) -> ordinalp (Vf f a).
   move => a asf; move: (Vf_target ff asf); rewrite tf.
   apply: (Os_ordinal ot).
have oifp: forall x y, inc x (source f) -> inc y (source f) ->
  (glt lo x y <-> (Vf f x) <o (Vf f y)).
   move => a b asf bsf; apply:(iff_trans (order_isomorphism_siso oisf asf bsf)).
   split.
     move => [] /ordo_leP [_ _ qa] pb; split => //;split;fprops.
   move => [[_ _ qd] qa]; split => //. 
   by apply/ordo_leP;split => //; rewrite tf; apply: (Vf_target ff).
have otf: ordinalp (target f) by ue.
have pb: forall t, inc t (source f) -> 
   (Vf f t) =c (Zo (source f) (fun z => (glt lo z t))).
  move => t tsf; symmetry;apply /card_eqP.
  set A := (Zo (source f) ((glt lo)^~ t)).
  have As: sub A (source f) by apply Zo_S.
  move: (Vf_target ff tsf) => wt.
  have ra: restriction2_axioms f A (Vf f t).
    split => //; [by  apply (ordinal_transitive otf wt) |  move => w ]. 
    move => /(Vf_image_P ff As) [u /Zo_P [usf lt] ->].
    by move: lt; rewrite (oifp _ _ usf tsf); move /oltP0 =>[_ _].
  move: (restriction2_fi injf ra).
  set g := restriction2 f A (Vf f t) => injg.
  have sg: source g = A by rewrite /g/restriction2; aw.
  have tg: target g = Vf f t by rewrite /g/restriction2; aw.
  exists g; split => //; split => //; split; first by fct_tac.
  rewrite sg tg; move=> y ytg. 
  move: (ordinal_transitive otf wt ytg) => ytf.
  move: (sjf _ ytf) => [w wsf wv]; move: (fp1 _ tsf) => ow.
  have wa: inc w A.  
    by apply: Zo_i => //; rewrite (oifp _ _ wsf tsf) - wv; apply /oltP.
  exists w => //; rewrite restriction2_V //.
have pc: forall t, inc t (source f) ->  cardinal (Vf f t) <c k.
  move => t tsf; rewrite (pb _ tsf).
  set S := (Zo (source f) ((glt lo)^~ t)).
  have qa: sub S (coarse (osucc (ord_pair_max t))).
    move => v /Zo_P [vs [/graph_on_P1 [_ _ le] _]];exact (ordering_pair3 le).
  move: (sub_smaller qa).
  move: tsf; rewrite sf low => tsf1.
  set a :=  (osucc ((ord_pair_max t))).
  rewrite /coarse - cprod2_pr1 - cprod2cl - cprod2cr.
  move=> le1; apply: (cle_ltT le1).  
  case: (finite_or_infinite (CS_cardinal a)) => fca.
     apply: clt_fin_inf => //.
     apply /NatP; apply: NS_prod; fprops.
  have ak : a <o k.
     apply /oltP => //.
     move: (infinite_card_limit2 ik) => [_ _]; apply.
     move: (tsf1) => /setX_P [_ i1 i2].
      by case: (ordering_pair1 (proj31 (pa _ tsf1))); move => [cd ->]. 
  move: ak (ak)  => [[oa _ _] _].
  move/ (ocle2P ck oa) => cak.
  move: (oclt cak) => lt1.
  by rewrite (hrec _ fca lt1).
rewrite -low - sf;split => //; saw.
have pd: sub (ordinal lo) k.
  move => t; rewrite - tf => ttf; move: (sjf _ ttf) => [v vsf ->].
  apply/(oltP ok) /(ocle2P ck (fp1 _ vsf)).
  exact: (pc _ vsf).
move: (card_bijection bf); rewrite sf low - cprod2_pr1 => pe.
rewrite tf; ex_middle xx.
have /(ocle2P ck otf) : target f <o k by  split => //; rewrite tf => //.
by move: (cleNgt (cprod_M1le ck (infinite_nz ik))); rewrite pe.
Qed.

Lemma infinite_product_alt x : infinite_c x -> x *c x = x.
Proof.
move => icx; move: (proj1 (proj1 icx)) => ox.
move: x ox icx; apply:least_ordinal2 => [x ox Hx] icx. 
have kl0: forall z, infinite_c z -> z <o x -> z *c z = z.
  by move => z icz zk;  apply: Hx.
move: (proj1 (infinite_product_aux icx kl0)) =>[bf sf tf].
by move:(card_bijection bf); rewrite sf tf - cprod2_pr1 (card_card(proj1 icx)).
Qed.

Lemma infinite_product_prop2 k
  (lo:= graph_on ord_pair_le (coarse k))
  (f := ordinal_iso lo):
  infinite_c k ->
  bijection_prop f (product k k) k /\
     (forall x y, inc x (source f) -> inc y (source f) ->
       (glt lo x y <-> (Vf f x) <o (Vf f y))).
Proof.
move => ik.
have pa: (forall z, infinite_c z -> z <o k -> z *c z = z).
  by move =>z iz _ ; apply:  infinite_product_alt.
exact:(infinite_product_aux ik pa).
Qed.

End FiniteSets. 
Export FiniteSets.
