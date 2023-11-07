(** * Theory of Sets : Ordinals
  Copyright INRIA (2011-2013 2108) Marelle Team (Jose Grimm).
*)

(* $Id: sset15.v,v 1.5 2018/09/04 07:57:59 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat. 
From gaia Require Export sset13c sset14.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Ordinals5.


Lemma infinite_power1 a b:  \2c <=c a -> a <=c (\2c ^c b) -> infinite_c b ->
   a ^c b = \2c ^c b.
Proof.
move=> le1 le2 ic.
have bb:= (cleR (proj1 ic)).
have ap:= nesym (proj2 (clt_leT clt_02 le1)).
move: (cpow_Mlele ap le2 bb)(cpow_Mlele card2_nz le1 bb).
rewrite - cpow_pow (csquare_inf ic).
apply: cleA.
Qed.


Lemma infinite_power1_a a b:  \2c <=c a -> a <=c b -> infinite_c b ->
   a ^c b = \2c ^c b.
Proof.
move => pa pb pc; apply: infinite_power1 => //.
exact: (cleT pb (proj1 (cantor (proj1 pc)))).
Qed.

Lemma infinite_power1_b x: infinite_c x ->  x ^c x = \2c ^c x.
Proof.
move => ix; apply: infinite_power1_a => //.
  apply: cle_fin_inf => //; apply /NatP; fprops.
exact (cleR (proj1 ix)).
Qed.

Lemma infinite_power1_c x: infinite_c x ->
  (cnext x) ^c x = \2c ^c x.
Proof.
move=> ix; move:(ix) =>[cx _].
apply: infinite_power1 => //;  last by apply: (cnext_pr3 cx).
exact: (cleT (cle_fin_inf finite_2 ix)  (proj1 ((cnext_pr2 cx)))).
Qed.


Lemma infinite_power1_d m: infinite_c m ->  omega0 ^c m = \2c ^c m.
Proof.
move => icm.
move/clt_omegaP: NS2 => [le2_omega _].
move/infinite_c_P2:(icm) => le1.
exact:(infinite_power1_a le2_omega le1 icm).
Qed.

Section Exercise3_3.
Variables f g :Set.
Hypothesis  (fgf: fgraph f)(fgg: fgraph g).
Hypothesis sd: domain f = domain g.
Hypothesis hg:  (allf g (fun x => \2c <=c x)).


Lemma compare_sum_prod0 a b : \2c <=c a -> \2c <=c b -> 
   a +c b <=c a *c b.
Proof.
move => ag2 bg2.
rewrite -(cdiff_pr ag2) cprodDl - csumA - csum_nn; set c := _ -c _.
rewrite - csumA (csumC _ b); apply:(csum_Mlele bg2).
apply:csum_Meqle.
exact:(cprod_M1le (CS_diff a \2c) (nesym(proj2(clt_leT clt_02 bg2)))).
Qed.


Lemma compare_sum_prod1: csum g <=c cprod g.
Proof.
case: (cleT_el  (CS_nat NS3) (CS_cardinal (domain g))); last first.
  move/(cltSleP NS2); case/cle_eqVlt.
    move/set_of_card_twoP => ddg; move: (ddg)=> [a [b [aneb vdg]]].
    have dd: doubleton_fam g (Vg g a) (Vg g b).
      by split => //; rewrite -{1} (Lg_recovers fgg) Lg_range vdg funI_set2.
    rewrite - (cprod2_pr dd)  -(csum2_pr dd).
    apply:(compare_sum_prod0); apply: hg; rewrite vdg; fprops.
  rewrite - succ_one;move/(cltSleP NS1); case/cle_eqVlt.
    move/set_of_card_oneP =>[x dgs].
    rewrite(cprod_trivial1 dgs)(csum_trivial1 dgs); apply:cleR; fprops.
  move/clt1 => /card_nonempty dge.
  rewrite (csum_trivial dge)(cprod_trivial dge); exact:cle_01.
move/ cardinal_ge3 =>[i [k1 [k2 [idg k1dg k2dg [ik1 ik2 k12]]]]].
rewrite /cprod /csum.
set Pr := (productb g); set (Sr := (disjointU g)).
suff [h2 [hp6 hp8]]: exists h2, 
  ( (forall j x, inc j (domain g) -> inc x (Vg g j) -> inc (h2 j x) Pr) 
  /\ (forall j k x y, inc j (domain g) ->inc k (domain g) ->
    h2 j x = h2 k y -> (x = y /\ j = k))).
  set hh:= Lf (fun z => h2 (Q z) (P z)) (disjointU g) (productb g).
  rewrite /Sr /Pr.
  have ->:  (disjointU g) = source hh by rewrite /hh; aw.
  have ->:  (productb g) = target hh by rewrite /hh; aw.
  apply: inj_source_smaller; apply: lf_injective.
    by  move=> z zf; move: (disjointU_hi zf) => [p1 p2 p3]; apply: hp6.
  move=> u v ud vd; move: (disjointU_hi ud) => [p1 p2 p3].
  move: (disjointU_hi vd) => [p4 p5 p6] eq. 
  by move: (hp8 _ _ _ _ p1 p4 eq) => [sp sq]; apply: pair_exten.
have gp j: inc j (domain g) -> inc \0c   (Vg g j) /\ inc \1c (Vg g j).
  move =>jdf; move: (proj33 (hg jdf)); rewrite - (proj2 (proj2 constants_v)).
  move => h; split; apply:h; fprops.
pose hh j x:= Lg (domain g) (fun z => Yo (z = j) x \0c).
have hp1: forall j x, inc j (domain g) -> inc x (Vg g j) -> inc (hh j x) Pr.
  move => j x jdf xv; apply /setXb_P;rewrite /hh; aw; split;fprops.
  move => z zdf. rewrite LgV//; Ytac zj; [ ue | exact:(proj1 (gp _ zdf))].
have hp2:  forall j x y, inc j (domain g) -> (hh j x = hh j y) -> x = y.
  by move=> j x y jdf sh;move:(f_equal (Vg^~j) sh);rewrite/hh !LgV//;Ytac0;Ytac0.
have hp3:  forall j k x y, inc j (domain g) -> inc k (domain g)-> j <> k ->
     (hh j x =  hh k y) -> (x = \0c /\  y = \0c).
  move=> j l x y jdf ldf jl sh;split.
    by move: (f_equal (Vg^~ j) sh); rewrite /hh !LgV//; Ytac0; Ytac0. 
  by move: (f_equal (Vg^~  l) sh); rewrite /hh !LgV//; Ytac0; Ytac0. 
pose h1 j := Lg (domain g) (fun z => Yo (z = j) \0c \1c).
have hp4: forall j, inc j (domain g) ->  inc (h1 j) Pr.
  move => j jdf; apply /setXb_P;rewrite /h1 Lgd;split;fprops.
  by move=> z zdf; rewrite LgV//; move:(gp _ zdf) => [za zb]; Ytac zj.
have hp5: forall j j', inc j (domain g) ->  (h1 j =  h1 j') -> j = j'.
  move=> j j' jdf  sh;ex_middle jj'; move: (f_equal (Vg ^~j) sh).
  by rewrite /h1 ! LgV//;Ytac0; Ytac0 => /esym e01; case: card1_nz.
pose h2 j x := Yo (x = \0c) (h1 j) (hh j x).
exists h2; split.
  move=> j x jdf xV; rewrite /h2; Ytac e1; [by apply: hp4 | by  apply: hp1].
have hp7: forall j k x, inc j (domain g) ->inc k (domain g) ->
  hh j x <>  h1 k.
  move=> j k x jdf kdf; rewrite /hh /h1.
  suff [z [zdf z1 z2]]: (exists z, [/\ inc z (domain g), z <> j & z <> k]).
    move=> eq; move: (f_equal (Vg ^~z) eq). 
    by rewrite !LgV//; Ytac0; Ytac0; fprops. 
  case: (equal_or_not j i) => ji.
    case: (equal_or_not k k1) => kk1.
    - exists k2; rewrite ji kk1;split; fprops.
    - exists k1; rewrite ji; split;fprops. 
  case: (equal_or_not k i) => kk1; last by exists i; split; fprops.
  case: (equal_or_not k1 j) => jk2.
     exists k2; rewrite kk1 - jk2; split; fprops.
  exists k1; rewrite kk1; split; fprops.
move=> j k x y jdf kdf; rewrite /h2; Ytac e1.
  Ytac e2.
    by move=>  sh1; move: (hp5 _ _ jdf sh1) => aux; rewrite e1 e2 aux. 
  by move => aux; case: (hp7 _ _ y kdf jdf).
Ytac e2 => sh1; first by case: (hp7 _ _ x jdf kdf).
case: (equal_or_not j k) => e3.
  split => //;rewrite e3 in sh1; apply: (hp2 _ _ _ kdf sh1). 
by move: (hp3 _ _ _ _ jdf kdf e3 sh1) => [aux1 aux2].
Qed.


Lemma compare_sum_prod2: 
  (forall i, inc i (domain f) ->  Vg f i <=c Vg g i) ->
  csum f <=c cprod g.
Proof.
move=> ale1.
exact: (cleT (csum_increasing sd ale1) (compare_sum_prod1)).
Qed.

Lemma compare_sum_prod3:
  (forall i, inc i (domain f) -> Vg f i <c Vg g i) ->
  csum f <c cprod g.
Proof.
move=> alt1.
have ale1:  (forall i, inc i (domain f) -> (Vg f i) <=c (Vg g i)).
  by move => i idf; move: (alt1 _ idf) => [ok _].
split; first by apply: compare_sum_prod2.
move /card_eqP=> [h [bh sh th]].
pose D i := (Vg f i) *s1 i.
have Dp1: forall i, inc i (domain f) -> sub (D i) (source h).
  move=> i idf t td; rewrite sh; apply /setUb_P.
  rewrite /disjointU_fam; aw; ex_tac; rewrite LgV//.
pose A i := Vfs h (D i).
have Dp2: forall i, inc i (domain f) -> (cardinal (A i)) <c (Vg g i).
  move: (bh)  => [ih _].
  move=> i idf;move: (alt1 _ idf) => aux. 
  rewrite /A (cardinal_image (Dp1 _ idf) ih) (cardinal_indexed).
  by rewrite (card_card (proj31_1 aux)). 
have fh: function h by fct_tac.
have Dp3: forall i, inc i (domain f) -> sub (A i) (target h).
  by move=> i idf; apply: fun_image_Starget1.
have Dp4: forall i F, inc i (domain f) -> sub F (target h) ->
  (cardinal (Vfs (pr_i g i) F)) <=c (cardinal F).
  rewrite th; move=> i F idf Fp; apply: surjective_cle.
  have idg: inc i (domain g) by ue.
  exists (restriction1 (pr_i g i) F).
  split => //; rewrite /restriction1; aw; trivial.
  apply: restriction1_fs; first by  apply: pri_f => //. 
  by rewrite /pr_i; aw.
have Dp5: forall i, inc i (domain f) -> 
  (cardinal (Vfs (pr_i g i) (A i))) <c (Vg g i).
  move=> i idf; exact:(cle_ltT (Dp4 _ _ idf (Dp3 _ idf)) (Dp2 _ idf) ).
have Dp6: forall i, inc i (domain f) -> exists xi, inc xi (Vg g i) /\
    (forall y, inc y (A i) -> Vf  (pr_i g i) y <> xi).
  move=> i idf; move: (Dp5 _ idf); set T := Vfs _ _.
  have fp: function (pr_i g i) by apply: pri_f => //; ue.
  have st: sub T (Vg g i).
    by move: (@fun_image_Starget1 _ fp (A i)); rewrite {2} /pr_i lf_target.
  rewrite -{1} (card_card (proj32_1 ( (alt1 _ idf)))); move=> [_ neq]. 
  ex_middle nex; case: neq;apply:f_equal; apply:extensionality =>//.
  have sAi: sub (A i) (source (pr_i g i)).
    by rewrite /pr_i; aw; rewrite -th; apply:  Dp3.
  move=> x xv; apply /(Vf_image_P fp sAi).
  ex_middle ney; case: nex; exists x; split => //.
  move=> y yA;case: (equal_or_not  (Vf (pr_i g i) y) x) => //.
  move=> wy; case: ney; ex_tac.
pose k i:= choose (fun xi => inc xi (Vg g i) /\
          (forall y : Set, inc y (A i) -> Vf (pr_i g i) y <> xi)).
have kp: forall i, inc i (domain f) -> 
   (inc (k i) (Vg g i) /\  (forall y, inc y (A i) -> Vf (pr_i g i) y <> (k i))).
  move=> i idf; apply choose_pr; apply: (Dp6 _ idf).
set x := Lg (domain g) k.
have xth: inc x (target h).
    rewrite th /x; apply /setXb_P; split;aww; move=> i idg; rewrite LgV//.
    by rewrite - sd in idg; move: (kp _ idg) => [p1 _].
move: bh => [ih sjh]; move: ((proj2 sjh) _ xth) => [y ysg Wy].
move: ysg; rewrite sh; move /setUb_P.
rewrite/disjointU_fam;aw.
move=> [i idf]; rewrite LgV// => yd.
have xA: inc x (A i).
  by rewrite /A Wy; apply /(Vf_image_P (proj1 ih)(Dp1 _ idf)); exists y. 
move: (kp _ idf) => [_ p2]; move: (p2 _ xA).
rewrite sd in idf; rewrite th in xth.
by rewrite pri_V // /x LgV.
Qed.

End Exercise3_3.

Lemma compare_sum_prod f g:
  fgraph f ->  fgraph g -> domain f = domain g ->
  (forall i, inc i (domain f) ->  Vg f i <c Vg g i) ->
  csum f <c cprod g.
Proof.
move=> fgf fgg sd ale1.
set K:= Zo (domain f) (fun i => \2c <=c  (Vg g i)).
have kdf: sub K (domain f) by apply: Zo_S.
have kdg: sub K (domain g) by ue.
have aux: forall i, inc i ((domain f) -s K) ->   
  (Vg f i = \0c /\  Vg g i = \1c).
  move=> i => /setC_P [idf] /Zo_P aux.
  have le1:=(ale1 _ idf).
  case: (cleT_el CS2 (proj32_1 le1)); first by move=> h; case: aux;split => //.
  rewrite - succ_one ; move /(cltSleP NS1) => h1.
  have p1:=(clt1 (clt_leT le1 h1)).
  split => //; apply: (cleA h1).
  by move: le1; rewrite p1; move/cge1P.
have pf:(forall i, inc i ((domain f) -s K) -> Vg f i = \0c).
   by move=> i ic; move: (aux _ ic) => [].
have pg:(forall i, inc i ((domain g) -s K) -> Vg g i = \1c).
  by rewrite - sd;move=> i ic; move: (aux _ ic) => [].
rewrite (csum_zero_unit kdf pf) (cprod_one_unit kdg pg).
apply: compare_sum_prod3; aww.
   by hnf; aw; move=> i iK; rewrite LgV//; move: iK => /Zo_P //; case.
by move=> i iK; rewrite !LgV//; apply: ale1; apply: kdf.
Qed.

Lemma exists_ordering X: cardinal_fam X ->
   exists f,
   [/\ bijection f, ordinalp (source f), target f = domain X &
     fg_Mle_lec (X \cf (graph f))].
Proof.
move => pb.
set d := domain X.
set w := Zo d (fun z => ~ (inc z z)).
case: (p_or_not_p (inc w d)) => wp. 
  case: (p_or_not_p (inc w w)) => h2; first by move: (h2) => /Zo_hi bad.
  by case: (h2); apply: Zo_i.
pose mzY Y z := (forall u, inc u Y -> Vg X z <=c Vg X u).
pose lev Y:= rep (Zo Y (mzY Y)).
have lep Y: sub Y d -> nonempty Y -> (inc (lev Y) Y /\ mzY Y (lev Y)).
  move => yd [y yY]; rewrite /lev; set T := Zo _ _.
  suff: nonempty T by move/rep_i => /Zo_P [].
  set Z := fun_image Y (Vg X).
  have neZ: nonempty Z by exists (Vg X y); apply /funI_P; exists y.
  have cZ: cardinal_set Z.
    by move => t /funI_P [z zy ->]; apply: pb; apply: yd. 
  move:(cle_wor' cZ neZ) => [/funI_P [t ty ->] qb].
  by exists t; apply: (Zo_i ty) => u uy; apply:qb; apply:funI_i.
pose lew Y:= Yo (nonempty (d -s Y)) (lev (d -s Y)) w.
have lewe Y: nonempty (d -s Y) ->
   (inc (lew Y)  (d -s Y) /\ mzY (d -s Y) (lew Y)).
  by move => ne; rewrite /lew; Ytac0; apply: lep => //; apply: sub_setC.
have lewb Y: inc (lew Y) (d +s1 w).
  apply/setU1_P;case: (p_or_not_p (nonempty (d -s Y))) => h. 
    by move: (lewe _ h) => [] /setC_P [ok _] _; left.
  by right;rewrite /lew; Ytac0.
move: (cantor (CS_cardinal d)); set a := _ ^c _ => lt1.
move: (proj32_1 lt1) => ca; move: (proj1  ca) => oa.
move: (ordinal_o_wor oa); set r := ordinal_o _ => wor.
have sr: substrate r = a by rewrite /r ordinal_o_sr.
pose lef f := lew (Imf f).
have ts: (forall f, function f -> segmentp r (source f) ->
      sub (target f)  (d +s1 w) ->  inc (lef f) (d +s1 w)).
  move=> f _ _ _; apply: lewb.
move: (transfinite_defined_pr lef wor); rewrite /transfinite_def sr.
move: (transfinite_definition_stable wor ts).
set f := transfinite_defined _ _; move=> stf [sjf sf fv].
have ff: function f by fct_tac.
pose R i := restriction1 f (segment r i).
have sRi i: inc i a ->  source (R i) = i.
  by   move => ia; rewrite  /R /restriction1  /r ordinal_segment; aw.
have fi: forall i, inc i a -> Vf f i <> w ->
  forall j, inc j i -> Vf f i <> Vf  f j.
  move => i ia fw; move: (fv _ ia); rewrite /lef.
  set E := (Imf (R i)) => eq1.
  move: eq1; case: (p_or_not_p (nonempty (d -s E))) => nt;
      last by rewrite /lew; Ytac0.
  move: (lewe _ nt) => [ /setC_P [_ s1]] _ eq j ji sv.
  case: s1; rewrite -eq sv /E.
  have sr1 := sRi _ ia.
  have sa1: sub (segment r i) (source f) by rewrite sf - sr ;apply: sub_segment.
  have ji1: inc j (segment r i).
    apply /segmentP; apply /ordo_ltP => //.
    by apply: (ordinal_transitive oa ia).
  apply /(Imf_P  (proj1 (restriction1_fs ff sa1))).
  by rewrite sr1;exists j => //; rewrite (restriction1_V ff sa1 ji1).
case: (p_or_not_p (inc w (target f))) => wt; last first.
  have bf: (bijection f).
    split; last by exact.
    split; [exact |  move => x y xsf ysf sv].
    case: (equal_or_not (Vf f x) w) => le1.
       case: wt; rewrite -le1; Wtac. 
    rewrite sf in xsf ysf.
    have ox:= (Os_ordinal oa xsf).
    have oy:= (Os_ordinal oa ysf).
    case: (oleT_ell ox oy) => //.
       move /(oltP oy) => lt2.
       by rewrite sv in le1;  move: (fi _ ysf le1 _  lt2); rewrite sv.
    by move /(oltP ox) => lt2; move: (fi _ xsf le1 _  lt2).
  have /sub_smaller: sub (target f) d.
    move=> t td; move: (stf _ td); case/setU1_P => // tw; case: wt;ue.
  by rewrite -(card_bijection bf) sf (card_card ca) => /(cltNge lt1).
pose pri i :=  (inc i (source f) /\ w = Vf f i).
have [i0 iv0]: exists i, pri i by move: ((proj2 sjf) _ wt) => [i0]; exists i0.
have oi0: ordinalp i0 by move: (proj1 iv0); rewrite sf; apply: (Os_ordinal oa).
move: (least_ordinal4 oi0 iv0). 
set qi :=least_ordinal _ _;move=> [oq [qsf qv] ql].
rewrite sf in qsf;move: qv; rewrite (fv _ qsf) /lef /lew. 
set e := Imf (R qi).
case: (p_or_not_p (nonempty (d -s e))) =>h qv.
  move: (lewe _ h) => [ /setC_P [wd _] _]; case: wp.
  by move: wd;rewrite /lew - qv.
have sr1 := sRi _ qsf.  
have sa1: sub (segment r qi) (source f) by rewrite sf - sr ;apply: sub_segment.
have fr:=(proj1 (restriction1_fs ff sa1)).
have pa1: forall i, inc i qi -> (inc (Vf f i) d /\  Vf f i <> w).
  move => t tq.
  move: (ordinal_transitive oa qsf tq); rewrite - sf => tf.
  case/setU1_P: (stf _ (Vf_target ff tf)) => qa.
    by split => // ww; case: wp; rewrite - ww.
  have prt : (pri t) by split.
  have h1:= (ql _ (Os_ordinal oq tq) prt).
  by move: tq => /(oltP oq) /(oleNgt h1).
have fv1 i: inc i qi -> Vf (R qi) i = Vf f i.
  move => iq. rewrite /R (ordinal_segment oa qsf)(restriction1_V ff) //.
  rewrite sf; apply:(ordinal_transitive oa qsf).
have de: d = e.
  set_extens t.
    move => qa; ex_middle tne; case: h; exists t; fprops.
  move /(Imf_P fr); rewrite sr1; move => [u uq ->].
  by rewrite (fv1 _ uq);  move: (pa1 _ uq) => [].
have ij1: forall i j, inc i qi -> inc j qi -> Vf f i = Vf f j -> i = j.
  move => i j iq jq sv.
  move: (pa1 _ iq) (pa1 _ jq)=> [_ xa1] [_ ya1].
  have ia:= ordinal_transitive oa qsf iq.
  have ja:=ordinal_transitive oa qsf jq.
  have oi:= Os_ordinal oa ia.
  have oj:= Os_ordinal oa ja.
  case: (oleT_ell oi oj) => //.
   by  move /(oltP oj) => lt2; move: (fi _ ja ya1 _  lt2); rewrite sv.
  by move /(oltP oi) => lt2; move: (fi _ ia xa1 _  lt2).
have ij2: injection  (R qi).
    split; first by exact.
    rewrite sr1;  move => x y xsf ysf /=.
    by rewrite (fv1 _ xsf) (fv1 _ ysf); apply: ij1.
move: (restriction_to_image_fb ij2).
set g := restriction_to_image (R qi) => bg.
have tg: target g  = d.
  by rewrite /g de /restriction_to_image/ restriction2; aw.
have osd: ordinalp (source g).
  by  rewrite /g  /restriction_to_image/ restriction2 sr1; aw.
have fg: function g by fct_tac.
have r2a: restriction2_axioms (R qi) (source (R qi)) (Imf (R qi)).
  by split => //; apply: Imf_Starget.
have gV : forall i, inc i qi -> Vf g i = Vf f i.
  move => i iq; rewrite/g /restriction_to_image restriction2_V // ? fv1 ? sr1//.
exists g; split => // u v.
rewrite composef_domain => us vs uv.
rewrite !composef_ev //;rewrite -/(Vf g u) -/ (Vf g v).
have aux: domain (graph g) = qi.
  rewrite (domain_fg fg) /g /restriction_to_image /restriction2 corresp_s. 
  by aw; rewrite sr1.
rewrite aux in us vs; rewrite (gV  _ us) (gV  _ vs).
move: (pa1 _ us) => [wfu wfuw].
case: (equal_or_not u v) => euv.
   by rewrite - euv; apply: cleR; apply: pb.
move: (ordinal_transitive oa qsf us) => ua.
rewrite (fv _ ua) /lef; set f0:= (R u).
case: (p_or_not_p (nonempty (d -s Imf f0))) => cle; last first.
  by case: wfuw; rewrite (fv _ ua) /lef -/f0 /lew; Ytac0.
move: (lewe _ cle); set x := lew _ ; move=> [qa qb].
suff: inc (Vf f v)(d -s (Imf f0)).
  move => qc; apply: (qb _ qc).
have sa2: sub (segment r u) (source f) by rewrite sf - sr ;apply: sub_segment.
have sr2 : (source f0)  = u by  apply: sRi.
have fr2:=(proj1 (restriction1_fs ff sa2)).
move: (pa1 _ vs) => [wfv _]; apply /setC_P;split => //.
move /(Imf_P fr2); rewrite sr2; move => [t tu].
have tu1: inc t (segment r u).
  by apply/segmentP; apply/ordo_ltP => //; move:(ordinal_transitive oa ua tu).
rewrite (restriction1_V ff sa2 tu1) => sv1; symmetry in sv1.
have tqi:=(ordinal_transitive oq us tu).
move: tu; rewrite  (ij1 _ _ tqi vs sv1).
by move /(oltP (Os_ordinal oa ua)) => /(oleNgt uv).
Qed.

Definition cardinal_pos_fam g := (allf g (fun z => \0c <c z)).

Lemma compare_sum_prod5  x  : 
  fgraph x -> cardinal_pos_fam x ->
  \csup (range x) <=c cprod x.
Proof.
move => fx  xi.
set A := Zo (domain x) (fun a => \2c <=c (Vg x a)).
have pa: (forall i, inc i ((domain x) -s A) -> (Vg x i) = \1c).
  move=> i /setC_P [idx ] /Zo_P h. 
  move: (xi _ idx) => [xx yy]; ex_middle x1; case: h; split => //.
  apply: (cge2 (proj32 xx) (nesym yy) x1). 
have Ax: sub A (domain x) by apply: Zo_S.  
set g := (Lg A (Vg x)).
have fgg: fgraph g by rewrite /g ; fprops.
have dg: domain g = A by rewrite /g; aw.
have gs: (forall i : Set, inc i (domain g) -> \2c <=c Vg g i).
  by rewrite /g dg => i iA; rewrite LgV//; move: iA => /Zo_P [_]. 
have cs: cardinal_set (range x).
  move => t /(range_gP fx) [z zy ->]; exact: (proj32_1(xi _ zy)).
move: (compare_sum_prod1 fgg gs); rewrite (cprod_one_unit Ax pa) - /g.
case: (emptyset_dichot A) => Ae.
  move: pa; rewrite Ae cprod_trivial0 setC_0 => h _.
  apply: (card_ub_sup CS1) => i/(range_gP fx) [t /h -> ->]; fprops.
apply: cleT.
have pb: (forall a, inc a (domain g) -> cardinalp (Vg g a)).
  by move => a /gs /proj32.
move: Ae => [a Aa]; move: (Aa) => /Zo_P [ay].
have ->: Vg x a = Vg g a by rewrite /g LgV.
rewrite -dg in Aa; move: (csum_increasing6 (pb _ Aa) Aa).
move => le1 le2; move: (cleT le2 le1) => le3.
apply: (card_ub_sup (proj32 le3)) => i /(range_gP fx) [j jdx ->].
have s1:= (cleT cle_12 le3).
case: (inc_or_not j A) => jA.
   rewrite -dg in jA; move: (csum_increasing6 (pb _ jA) jA).
   rewrite {1}/g LgV//; ue.
have jc: inc j ((domain x) -s A) by apply /setC_P. 
by rewrite (pa _ jc).
Qed.

Lemma infinite_increasing_power_bound0 X: 
  fgraph X -> cardinal_fam X ->
  cprod X <=c (\csup (range X)) ^c (cardinal (domain X)).
Proof.
move => fX hb .
rewrite cpowcr - cprod_of_same /cst_graph; apply: cprod_increasing; aww.
move => x idx;rewrite LgV //.
apply: card_sup_ub.
  move => t tx; move: tx => /(range_gP fX) [z zi ->]; apply: (hb _ zi).
apply: (inc_V_range fX idx).
Qed.

Lemma infinite_increasing_power_bound1 X: 
  fgraph X -> ordinal_fam X -> 
  cprod (Lg (domain X) (fun z => \aleph (Vg X z))) <=c
  \aleph (\osup (range X)) ^c (cardinal (domain X)).
Proof.
move => fX ogx.
set Y := Lg _ _.
case: (emptyset_dichot (domain X)) => xne.
  rewrite /Y xne cprod_trivial;aw; trivial.
  rewrite cardinal_set0 cpowx0; fprops.
have <- : \osup (range Y) = \aleph (\osup (range X)).
   apply:(sup_range_aleph fX ogx xne).
have -> : domain X = domain Y by rewrite /Y; aw.
apply:infinite_increasing_power_bound0; rewrite/Y; fprops; hnf; aw.
move => i idx; rewrite LgV//; fprops.
Qed.

  
Lemma infinite_increasing_power4 X (Y:= Lg (domain X)(fun z => \aleph (Vg X z)))
  (a := \osup (range X)):
  ofg_Mlt_lto X -> limit_ordinal (domain X) -> 
  (cardinal (domain X) <=c \aleph a /\  \aleph a <c (cprod Y)).
Proof.
move => pa pb.
move: (increasing_sup_limit4 pa pb);rewrite -/Y -/a; move => [pc pd pe].
move: pa => [fgx xo xi].
move: (pc)(pb) => [oa _ _] [odx _ ldx].
have pa: cardinal (domain X) <=c (cardinal a).
  have:bijection (Lf (Vg X) (domain X) (range X)).
    apply: lf_bijective.
        move => t td; apply /(range_gP fgx); ex_tac.
      move => u v ud vd sv.
      case: (oleT_ell (Os_ordinal odx ud)(Os_ordinal odx vd)) => // cuv.
        by move: (xi _ _ ud vd cuv); rewrite sv;move => [_].
      by move: (xi _ _ vd ud cuv); rewrite sv;move => [_].
    move => y  /(range_gP fgx) [x xd ->]; ex_tac.
  move/card_bijection; aw => ->; apply: (sub_smaller pd).
move: (ocle1  (aleph_pr6 oa)); rewrite (card_card (CS_aleph oa)) => lt1.
move: (cleT pa lt1) => le1 {pa lt1}.
split; first by exact.
have ia:=(CIS_aleph (proj31 pc)).
have cfy: cardinal_fam Y.
  rewrite /Y;hnf;aw; move => i idx; rewrite LgV//; apply: CS_aleph;fprops.
have fgY: fgraph Y by rewrite /Y; fprops.
have cd1: cardinal (domain Y) <=c \aleph a by rewrite /Y; aw.
have <-: csum Y = \aleph a.
  by rewrite /Y - pe; apply: csum_of_small_b4 => //; rewrite  pe.
set Z := Lg (domain X) (fun z => (\aleph (Vg X (osucc z)))).
have fgZ: fgraph Z by rewrite /Z; fprops.
have sd:  domain Y = domain Z by rewrite /Y /Z; aw.
have inc1: (forall i, inc i (domain Y) -> Vg Y i <c Vg Z i).
  rewrite /Y/Z; aw; move => i idx; rewrite !LgV//; apply: aleph_lt_ltc.
  apply: xi => //; [ by apply: ldx | apply: (oltS (Os_ordinal odx idx)) ].
apply: (clt_leT (compare_sum_prod fgY fgZ sd inc1)).  
set X1 := fun_image (domain X) osucc.
have scx1: sub X1 (domain X) by move =>t /funI_P [z zd ->]; apply: ldx.
have <-: cprod (restr Y X1) = cprod Z.  
  have ->: cprod (restr Y X1)  = cprodb X1 (fun z => \omega (Vg X z)).
    by apply:cprodb_exten => i ii; rewrite /Y; aw; rewrite LgV//; apply: scx1.
  rewrite /Z -/(cprodb  _ _); apply:cprod_Cn2; split.
  +  move => t td; apply /funI_P; ex_tac.
  + move => u v ud vd. 
    exact: (osucc_inj (Os_ordinal odx ud)(Os_ordinal odx  vd)).
  + by move => y /funI_P.
apply: cprod_increasing1 => //; last by rewrite  /Y; aw.
by hnf;rewrite /Y; aw;move => x xd; rewrite LgV//; apply: aleph_nz; apply: xo.
Qed.

Lemma infinite_increasing_power5 X (Y:= Lg (domain X)(fun z => \aleph (Vg X z)))
  (a := \osup (range X)):
  ofg_Mlt_lto X -> limit_ordinal (domain X) -> 
  [/\  \aleph a <c cprod Y,
     cprod Y <=c \aleph a ^c cardinal (domain X) &
     \aleph a ^c cardinal (domain X) <=c \2c ^c \aleph a].
Proof.
move => pa pb.
move: (infinite_increasing_power4 pa pb) => [qa qb].
move: (increasing_sup_limit4 pa pb);rewrite -/Y -/a; move => [pc pd pe].
move: pa => [fgx xo xi].
move: (infinite_increasing_power_bound1 fgx xo); rewrite -/Y -/a => le1.
split; [exact | exact |].
move: (cpow_Meqle (aleph_nz (proj31 pc)) qa).
rewrite -/a infinite_power1_b //; apply: (CIS_aleph (proj31 pc)).
Qed.

Lemma infinite_increasing_power x (y := domain x):
   fgraph x -> infinite_c y ->  cardinal_pos_fam x ->
   fg_Mle_lec x ->
   cprod x = (\csup (range x)) ^c y.
Proof.
move => fx cy alz xi.
have osr: cardinal_set (range x).
  move => t /(range_gP fx) [z zy ->]; exact: (proj32_1(alz _ zy)).
apply: cleA.
rewrite - cprod_of_same /cst_graph; apply: cprod_increasing => //; aww. 
  move=>t td; rewrite LgV//. 
  by apply: card_sup_ub => //; apply /(range_gP fx); ex_tac.
move: (infinite_product_prop2 cy); set f := ordinal_iso _.
move => [[bf sf tf] fp].
set g:= Lg y (fun z=> fun_image y (fun t => (Vf f (J t z)))).
have ff: function f by fct_tac.
have pa: partition_w_fam g (domain x).
  rewrite /g; split;fprops.
     apply: mutually_disjoint_prop; aw.
     move=> i j z iy jy; rewrite !LgV//. 
     move=> /funI_P [a ay av] /funI_P [b iby bv].
     rewrite av in bv. 
     have asf: inc (J a i) (source f) by rewrite sf; fprops.
     have bsf: inc (J b j) (source f) by rewrite sf; fprops.
     exact (pr2_def (bij_inj bf asf bsf bv)).
   set_extens t. 
     move /setUb_P; aw; move => [a ay];rewrite LgV//;move /funI_P => [b ny ->]. 
     rewrite -/y -tf; Wtac; rewrite sf; fprops.
   rewrite -/y -tf => ytf; move: (bij_surj bf  ytf) => [z zs zv].
   move: zs; rewrite sf => /setX_P; rewrite -tf; move => [pz za zb].
   apply /setUb_P; exists (Q z) => //;aw;trivial;rewrite LgV//; apply /funI_P. 
   by exists (P z) => //; rewrite  pz.
rewrite (cprod_An pa).
rewrite {1} /g; aw.
rewrite - cprod_of_same /cst_graph; apply: cprod_increasing => //;aw; trivial.
move=> a ay; rewrite LgV // LgV //.
set h :=  (restr x (Vg g a)).
have fgr: fgraph h by rewrite /h;fprops.
have s1:  sub (Vg g a) (domain x). 
  rewrite /g => t; rewrite LgV//; move /funI_P => [z zy ->]; rewrite -/y - tf.
  Wtac; rewrite sf; fprops.
have pb: (forall b, inc b (domain h) -> \0c <c Vg h b).
   rewrite /h restr_d // => b bv.
   rewrite restr_ev //; exact: (alz _  (s1 _ bv)).
move: (compare_sum_prod5 fgr pb); rewrite -/h => le1.
have csh: cardinal_set (range h).
  move => t /(range_gP fgr) [u ud ->]; exact: (proj32_1 (pb _ ud)).
apply: (cleT _ le1).
apply card_ub_sup => //; first by apply: CS_sup.
move => i  /(range_gP fx) [j jdx ->].
rewrite -/y -tf in jdx; move:(bij_surj bf jdx) => [z zf ->].
move: (zf); rewrite sf => /setX_P [pz py qy].
move: (infinite_card_limit2 cy) => [oy _ yp]. 
have op: ordinal_pair z by split => //; apply: (Os_ordinal (proj1 (proj1 cy))).
set b0 := (ord_pair_max z); set b := osucc b0.
have ib0y: inc b0 y by  rewrite /b0;case: (ordering_pair1 op); move=> [_ -> ].
have iby: inc b y  by apply yp. 
move: (Os_ordinal oy iby) (Os_ordinal oy ay) => ob oa.
have opab: ordinal_pair (J b a) by split => //; aww.
have bsba:= (proj1 (omax_p1 ob oa)).
have ult: ord_pair_max z <o omax b a.
  apply: (olt_leT _ bsba); exact (oltS (Os_ordinal oy ib0y)).
have nzj: z <> J b a. 
  by move => zj; case: (proj2 ult); rewrite zj/ord_pair_max; aw.
have sa: inc (Vf f (J b a)) (Vg g a) 
   by rewrite /g LgV//; apply /funI_P; ex_tac.
have wy: inc (Vf f z) y by  rewrite - tf; Wtac.
have wy': inc (Vf f (J b a)) y by rewrite - tf; Wtac; rewrite sf; fprops.
have jsf: inc (J b a) (source f) by rewrite sf; fprops.
have sb: Vf f z <o Vf f (J b a).
  rewrite -(fp _ _  zf jsf); split => //.
  have hw:ord_pair_le z (J b a) by split => //; left; rewrite /ord_pair_max; aw.
  rewrite/coarse;apply /graph_on_P1; split; fprops; apply /setX_P;split => //.
apply: (cleT  (xi _ _ wy wy' (proj1 sb))).
apply: card_sup_ub => //; apply /(range_gP fgr).
exists (Vf f (J b a)); rewrite /h => //; aw;trivial; rewrite LgV//.
Qed.



Lemma power_cofinality x: \2c <=c x -> x <c  x ^c (cofinality_c x).
Proof.
move=> x1; move: (cofinality_c_rw x1) => [pb pc _].
move: pc => [f [[pc pd] pe pf]].
set g := cst_graph (domain f) x.
have pg: fgraph g by rewrite /g/cst_graph; fprops.
have ph: domain f = domain g by rewrite /g/cst_graph; aw.
have pi: (forall i, inc i (domain f) -> (Vg f i) <c (Vg g i)).
  by move=> i idf; rewrite /g/cst_graph LgV//;apply:pd.
by move: (compare_sum_prod pc pg ph pi); rewrite [cprod g] cprod_of_same pe pf.
Qed.

Lemma power_cofinality1 x: infinite_c x -> x <c  x ^c (\cf x).
Proof.
move => icx; rewrite -(cofinality_card icx); apply: power_cofinality.
by apply: infinite_ge2.
Qed.

Lemma power_cofinality2 x: infinite_c x  -> x <c \cf (\2c ^c x).
Proof.
move=> xi;move: (infinite_pow2 xi) => iy.
have ynz:= infinite_nz iy.
have ia := (cofinality_infinite_cardinal iy).
case: (cleT_el (proj1 ia) (proj1 xi)) => le2 //.
case: (cltNge (power_cofinality1 iy)).
rewrite -{3} (csquare_inf xi) cpow_pow; exact:(cpow_Meqle ynz le2). 
Qed.

Lemma power_cofinality3: aleph0 <c \cf (\2c ^c aleph0).
Proof.
apply: power_cofinality2; split;by [apply: CS_omega | apply: OIS_omega].
Qed.

Lemma power_cofinality5 x y: \2c <=c x -> infinite_c y ->
  y <c \cf (x ^c y).
Proof.
move => x2 icy.
have cx:= proj32 x2.
case: (cleT_ee cx (proj1 icy)) => aux.
  by rewrite (infinite_power1_a x2 aux icy);apply: power_cofinality2.
have icx := (cle_inf_inf icy aux).
have pi:= (CIS_pow2 icx icy).
move:(power_cofinality1 pi). set c :=  (\cf x ^c y).
rewrite - cpow_pow => lt1.
move:(cofinality_infinite_cardinal pi) => ww.
case: (cleT_el (proj1 ww) (proj1 icy)) => // cy.
case: (proj2 lt1);rewrite (cprod_inf cy icy (infinite_nz ww)) //.
Qed.

Lemma infinite_power7b x y: 
  infinite_c x -> y <c \cf x -> 
  x ^c y <=c cardinal (unionb (Lg x (functions y))).
Proof.
move=> icx yc.
have cx:= proj1 icx.
have ox:= OS_cardinal cx.
have Ha f: (function_prop  f y x) -> ordinal_set (Imf f).
  move => [ff sf tf] t /(Imf_P ff)  [u usf ->].
  by apply: (Os_ordinal ox); rewrite - tf;Wtac.
have ha:(forall f, function_prop f y x -> inc (\osup (Imf f)) x).
  move => f fp; move: (fp) => [ff sf tf].
  move:(Ha _ fp);set T := (Imf f) => osT.
  have ou: ordinalp (union T) by apply: OS_sup.
  apply /(oltP ox);case: (oleT_el ox ou) => // le1.
  have eq1: union T = x.
    apply: oleA => //; apply: ord_ub_sup => //.
    move=> i =>  /(Imf_P ff)  [u usf ->].
    by move: (Vf_target ff usf); rewrite tf => /(oltP ox) [].
  have cox:  cofinal_function_ex x y.
    exists f; split => // t tx.
    have ls: t <o \osup T by apply /(oltP ou); ue.
    move: (olt_sup osT ls) => [z  /(Imf_P ff) [u usf ->] [tw _]].
    rewrite - sf; ex_tac.
  have oy:= (proj1 (proj31_1 yc)).
  case: (oleNgt ((proj33 (cofinality_rw ox))  _ oy cox) (oclt yc)).
pose sf f := \osup (Imf f).
pose sf1 f := osucc (sf f).
have pa: forall f, inc f (functions y x) -> (sf1 f) <o x.
  have qc:= (proj33 (infinite_card_limit2 icx)).
  move => f /functionsP fp; apply /(oltP ox); apply: qc; exact: (ha _ fp).
have pb:forall f, inc f (functions y x) -> 
  (forall t, inc t (source f) -> inc (Vf f t) (sf1 f)).
  move => f /functionsP fpp t tsf. 
  have osT := (Ha f fpp).
  apply /oleP; first by apply: OS_sup.
  apply: ord_sup_ub => //; apply /(Imf_P (proj31 fpp)); ex_tac.
pose R f := restriction2 f (source f) (sf1 f).
have pc: forall f, inc f (functions y x) ->
  restriction2_axioms f (source f) (sf1 f).
  move=> f fp; move: (fp) => /functionsP [qc qd qe].
  split => //.
    by rewrite qe; move: (pa _ fp) => [[_ _ ok] _]. 
  by move=>t /(Imf_P qc) [u usf ->]; apply: (pb _ fp).
have pd: forall f, inc f (functions y x) ->
    inc (R f) (functions y (sf1 f)).
  move=> f fh; move: (restriction2_prop (pc _ fh)) => [p1 p2 p3].
  apply /functionsP;split => //; rewrite /R p2. 
  by move: fh => /functionsP [q1 q2 q3].
set t1:= unionb _.
have pe: forall f, inc f (functions y x) ->  inc (R f) t1.
  move=> f fi; move: (pd _ fi) => sa.
  have sb:inc (sf1 f) x by apply /(oltP ox); exact: (pa _ fi).
  apply /setUb_P; aw;  exists (sf1 f) => //; rewrite LgV//.
set g := Lf R  (functions y x) t1.
suff ig: injection g by move: (inj_source_smaller ig); rewrite /g; aw.
apply: lf_injective => // u v us vs eq.
move: (pc _ us) (pc _ vs) => axf axg.
move: us vs => /functionsP [fu su tu] /functionsP [fv sv tv].
apply: function_exten => //; try ue.
move => t tsu; move: (f_equal (Vf ^~ t) eq);rewrite /R restriction2_V  //.
by rewrite restriction2_V  // sv - su.
Qed.

Lemma infinite_power2 n m (x:=\aleph n) (y:= \aleph (osucc n)):
   ordinalp n -> m <> \0c -> 
   y ^c m = (x ^c m) *c y.
Proof.
move => on mnz.
rewrite -(cpowcr) -(cpowcr x);set m':= cardinal m.
have cm': cardinalp m' by  rewrite /m'; fprops.
have m'nz:=(card_nonempty0 mnz).
have osn:= (OS_succ on).
move: (CIS_aleph on) (CIS_aleph osn) (aleph_pr10c on).
rewrite -/x -/y => icx icy ap.
have m1: \1c <=c m' by  apply: cge1; fprops.
have p1: forall z, ordinalp z -> (\aleph z) <=c ((\aleph z) ^c m').
  move=> z oz; move: (CIS_aleph oz) => iz; move: (iz) => [cz _].
  apply: cpow_Mle1 => // coz.
have ipx: infinite_c (x^c m') by apply: (CIS_pow).
move: (ap) => [lexy _].
have cxy := (cpow_Mleeq m' (proj1 ap) (aleph_nz on)).
move: (icy) => [cy _]; move:(cy) => [oy _].
apply: cleA; last first.
  by apply: cprod_inf4 => //; [apply: p1 | apply:CIS_pow].
case: (cleT_el cy cm') => cmx.
  have im:= (cle_inf_inf icy cmx).
  have lex2:=(infinite_ge2 icx).
  rewrite (infinite_power1_a lex2 (cleT lexy cmx) im).
  rewrite (infinite_power1_a (cleT lex2 lexy) cmx im).
  apply: cprod_M1le => //; fprops.
  apply: (aleph_nz (OS_succ on)).
have ha: m' <c \cf y. 
  by move: (regular_initial_successor on) => /regular_cardinalP [_ ->].
have hb:= (infinite_power7b icy ha).
apply: (cleT hb); apply: (cleT (csum_pr1 (Lg y (functions m')))).
rewrite /csumb; aw; set f := Lg _ _. 
have df: domain f = y by rewrite /f; aw.
rewrite - df /f; apply:csum_of_small_b1.
split; [ fprops | hnf; aw; move =>i ix; rewrite !LgV//].
rewrite -/(cpow i m') - cpowcl.
case: (equal_or_not (cardinal i) \0c) => iz.
   by rewrite iz (cpow0x m'nz);apply: cle0x; rewrite /cpow; fprops.
by apply: (cpow_Mleeq _ _ iz);apply: (aleph_pr12d on); apply /(oltP oy).
Qed.


Lemma infinite_power2_bis x (y:= cnext x) m:
  infinite_c x -> m <> \0c -> 
   y ^c m = (x ^c m) *c y.
Proof.
move=> ix mnz; rewrite /y;move: (ord_index_pr1 ix)=> [on <-].
rewrite (cnextE on); apply: (infinite_power2 on mnz).
Qed.


Lemma infinite_power3 n m (x:=\aleph n):
   natp n -> m <> \0c -> 
   x ^c m = (\2c ^c m) *c x.
Proof.
move=> nN mz. 
rewrite - (cpowcr x m) - (cpowcr \2c m).
set m':= cardinal m.
have cm': cardinalp m' by  rewrite /m'; fprops.
have m'nz:= (card_nonempty0 mz).
rewrite /x; clear x.
case: (finite_or_infinite cm') => fm.
  have mN: natp m' by apply /NatP.
  have on:=(OS_nat nN).
  have io:=(CIS_aleph on).
  rewrite (cpow_inf io mN m'nz)  cprodC.
  symmetry; apply: cprod_inf => //; last by apply: cpow2_nz. 
  apply: cle_fin_inf => //. 
  apply /NatP; apply: NS_pow; fprops.
have io: infinite_c omega0 by rewrite - aleph0E; apply: CIS_aleph; fprops.
have pa: \2c <=c omega0 by apply: infinite_ge2.
have onz:= omega_nz.
move: n nN; apply: Nat_induction.
  move: (infinite_pow2 fm)  => px; move/infinite_c_P2: (px) => le2.
  rewrite aleph0E (infinite_power1_d fm) cprod_inf //.
move=> n nN hrec.
rewrite succ_of_finite; last by apply /NatP.
have on:= (OS_nat nN).
rewrite (infinite_power2 on m'nz) hrec - cprodA.
have pc := proj1 (aleph_pr10c on).
move: (cprod_inf pc (CIS_aleph (OS_succ on)) (aleph_nz on)).
by rewrite cprodC;  move => ->.
Qed.


Lemma aleph_pow_prop1: aleph1 ^c aleph0 = aleph1 ->
  forall n, natp n -> n <> \0c -> (\aleph n) ^c aleph0 = \aleph n.
Proof.
move => H0 n nN nz.
move: (cpred_pr nN nz) => [ cp ->]; move: (cpred n) cp; clear n nN nz.
apply: Nat_induction; first by rewrite succ_zero.
move => n nN. 
rewrite (succ_of_nat (NS_succ nN)) (succ_of_nat nN) => Hrec.
have on :=(OS_nat nN).
have osn := (OS_succ on).
rewrite (infinite_power2 osn omega_nz) Hrec cprodC cprod_inf //.
- by apply: aleph_le_lec; apply /oleSSP; apply: (oleS on).   
- exact: (CIS_aleph (OS_succ osn)).
- exact: (aleph_nz osn).
Qed.

Lemma infinite_power4 a (b:= \2c ^c a): infinite_c a ->
  [/\ b ^c a = b, b ^c a <c (cnext b) ^c a, 
    (forall c, \2c <=c c -> c ^c a = c -> b <=c c) &
     (forall c, infinite_c c -> c ^c a <c (cnext c) ^c a -> b <=c c)].
Proof.  
move=> ica. 
have anz: a <> \0c by apply: infinite_nz.
have ib: infinite_c b by apply: infinite_pow2.
have p1: b ^c a = b by rewrite/b - cpow_pow csquare_inf.
have p3: (forall c, \2c <=c c -> c ^c a = c -> b <=c c).
   move =>c c2 cp.
   have cc:=proj32 c2.
   case: (cleT_el (proj1 ib) cc) => //; move=> [le1 ne1].
   move: (infinite_power1 c2 le1 ica); rewrite cp -/b //.
have p2: b ^c a <c cnext b ^c a.
  move: (proj32 (cnext_pr1 (proj1 ib))).
  rewrite (infinite_power2_bis ib anz) p1 => h; move: (proj1 h) => le1.
  move: (infinite_nz ib) => bnz.
  have isc: infinite_c (cnext b) by  apply: (cle_inf_inf ib le1).
  by rewrite cprodC (cprod_inf le1 isc bnz).
split => //.
move=> c ic; rewrite (infinite_power2_bis ic  anz) => ha.
have c1: cardinalp (c ^c a) by fprops. 
have c2 := (CS_cnext (proj1 ic)).
case:  (cleT_el c2 c1) => h.
  have ip: infinite_c (c ^c a) by apply: CIS_pow2.
  by move: (cleNgt (cprod_inf1 h ip) ha).
move: (cnext_pr4 (proj1 ic) h) => h1.
apply: (p3 _ (infinite_ge2 ic)).
apply: cleA => //; apply: (cpow_Mle1 (proj32 h1) anz). 
Qed.

Lemma infinite_power5 n p m (x:=\aleph n) (y:= \aleph (n +o p)):
   ordinalp n -> ordinalp p -> m <> \0o -> 
   cardinal p <=c m ->
   y ^c m = (x ^c m) *c (y ^c (cardinal p)).
Proof.
move=> on op mnz cpm.
have cm := (proj32 cpm).
have ca: cardinalp (x ^c m) by rewrite /cpow; fprops.
pose hyp p:= cardinal p <=c m ->
  \aleph (n +o p) ^c m = x ^c m *c \aleph (n +o p) ^c (cardinal p).
case:(least_ordinal6 hyp op); first by apply.
set q :=least_ordinal _ _; move=> [oq pb] [] pa.
have xnz: x <> \0c by apply: aleph_nz.
move: (pa); rewrite - {1} (card_card cm) => pa'.
case: (ordinal_limA oq) => h.
   by rewrite h cardinal_set0 (osum0r on) cpowx0 cprod1r.
  move:h=> [r or qv].
  rewrite qv - osum2_succ //.
  have rq1: inc r q by rewrite qv; fprops.
  have cq:= (cleT (sub_smaller (ordinal_transitive oq rq1)) pa).
  move: (pb _ rq1 cq).
  set y1 := \aleph (n +o r); set y2 := \aleph (osucc (n +o r)).
  have onr: ordinalp (n +o r) by fprops.
  move: (infinite_power2 onr mnz); rewrite  -/y1 -/y2 cpowcr => r1 r2.
  have osnr: ordinalp (osucc (n +o r)) by fprops.
  have cy1m: cardinalp (y1 ^c m) by rewrite /cpow; fprops.
  have icy2: infinite_c y2 by apply: CIS_aleph.
  have icy1: infinite_c y1 by apply: CIS_aleph.
  have icx: infinite_c x by apply: CIS_aleph.
  have y1nz: y1 <> \0c by apply: aleph_nz.
  have y2nz: y2 <> \0c by apply: aleph_nz.
  move: (icy1) (icy2) (icx) => [cy1 _ ] [cy2 _] [cx _].
  have le1 :=(cpow_Mleeq m (aleph_le_lec (osum_Mle0 on or)) xnz).
  have le0 := (aleph_le_lec(proj1 (oltS (OS_sum2 on or)))).
  have le2:= (cpow_Mleeq m le0 y1nz). 
  move: (cpow_Meqle y2nz pa'); rewrite !cpowcr qv => lexx.
  have paa:=(cpow_Mle1 (proj1 icx) mnz).
  have icxm:= (cle_inf_inf icx paa).
  have icy1m:= (cle_inf_inf icxm le1).
  have icy2m:= (cle_inf_inf icy1m le2).
  have y1mnz:=(cpow_nz y1nz (b:=m)).
  have xmnz := (cpow_nz xnz (b:=m)).
  case: (cleT_ee cy1m cy2) => r3.
    move: (cprod_inf r3 icy2 y1mnz).
    rewrite cprodC; move=> h; rewrite h in r1.
    rewrite r1; rewrite r1 in lexx.
    rewrite (cleA lexx  (cpow_Mle1 cy2 (@osucc_nz r))).
    have r6: x ^c m <=c y2 by  rewrite -r1; apply:cleT le1 le2.
    by rewrite cprodC (cprod_inf r6 icy2 xmnz).
  have r4 :=  (cprod_inf r3 icy1m y2nz).
  rewrite r4 in r1.
  have r6:= (cpow_nz y2nz (b := (osucc r))).
  case: (equal_or_not (x ^c m) (y1 ^c m)) => r7.
    by rewrite r7 -r1 (cprod_inf lexx icy2m r6).
  have r9: y1 ^c m = y1 ^c r.
    case:(cleT_ee (proj32 paa) (CS_pow y1 r)) => h.
      by rewrite r2 cprodC(cprod_inf h  (cle_inf_inf icxm h) xmnz).
    by case: r7;rewrite - (cprod_inf h icxm (cpow_nz y1nz (b := r))) r2.
  have crr1:cardinal r <=c cardinal (osucc r).
      apply: sub_smaller; rewrite /osucc; fprops.
  move: (cpow_Mlele y1nz le0 crr1); rewrite !cpowcr -r9 -r1 => le3.
  by rewrite (cleA lexx le3) cprodC (cprod_inf (cleT le1 le2) icy2m xmnz).
have onq:=(OS_sum2 on oq). 
apply cleA; last first.
   move: (CIS_pow (CIS_aleph onq) mnz) => r1.
   have r2 :=(cpow_Mleeq m (aleph_le_lec (osum_Mle0 on oq)) xnz).
   apply: (cprod_inf4 r2 _ r1);apply: cpow_Meqle => //; apply: (aleph_nz onq).
set E := (fun_image q (fun z =>  \aleph (n +o z))).
set f := Lg q (fun z => \aleph (n +o z)).
have r2: E = range f by rewrite Lg_range.
have r1 :  \aleph (n +o q) = \osup E.
  move: (normal_ofs_compose  aleph_normal (osum_normal on)) => [xa xb].
  by move: (xb _ h) => /= ->. 
have fgf: fgraph f by rewrite /f; fprops.
have r3: forall i, inc i (domain f) -> \2c <=c Vg f i.
   rewrite /f; aw; move=> i idf; rewrite LgV//; apply: infinite_ge2.
   apply: CIS_aleph; apply: (OS_sum2 on (Os_ordinal oq idf)).
have r4: \aleph (n +o q) = csum f.
  rewrite r1 r2 - csum_of_small_b4 //.
  - move=> a ad; exact: (proj32 (r3 _ ad)).
  - by rewrite -r2 -r1; apply: CIS_aleph.
  - rewrite - r2 -r1 /f; aw.
    apply:cleT (aleph_le_lec (osum_M0le on oq)).
    rewrite - (card_card (CS_aleph oq)); exact: (ocle1 (aleph_pr6 oq)).
have r5: \aleph (n +o q) <=c cprod f.
   rewrite r4; apply: compare_sum_prod2 => //.
   move=> i idf; move: (r3 _ idf) => [_ c _]; fprops.
move: (cpow_Mleeq m r5 (aleph_nz onq)).
rewrite cpow_prod {1} /f Lgd /cprodb. 
have ->: (Lg q (fun i => Vg f i ^c m)) = 
   Lg q (fun t => x ^c m *c \aleph (n +o t) ^c (cardinal t)).
  apply: Lg_exten; move=> t tq.
  have tq1: t <o q by apply /(oltP oq).
  rewrite /f LgV//; apply (pb _ tq); apply: (cleT _ pa).
  apply:(ocle1 (proj1 tq1)).
rewrite -/(cprodb q _) -prod_of_prods cprod_of_same - cpow_pow. 
have icq: infinite_c (cardinal q).
  apply: (cle_inf_inf CIS_omega).
  by move:(sub_smaller (proj33 (limit_ge_omega h))); rewrite cardinal_Nat.
have ->: (m *c q) = m.
  have icm:= (cle_inf_inf icq  pa).
  move: (cprod_inf pa icm (infinite_nz icq)).
  by rewrite cprod2cr. 
set f2:= \aleph (n +o q) ^c (cardinal q).
set ff:= (fun i => \aleph (n +o i) ^c (cardinal i)).
move => r6.
have: cprod (Lg q ff) <=c f2 ^c (cardinal q).
   rewrite  cpowcr - cprod_of_same /cst_graph.
   apply: cprod_increasing; aw; trivial.
   move=> t tq; rewrite (LgV tq) (LgV tq).
   have [tq1 _]: t <o q by apply /oltP.
   apply: cpow_Mlele  (ocle1 tq1).
     apply: (aleph_nz (OS_sum2 on (proj31 tq1))).
   exact: (aleph_le_lec (osum_Meqle tq1 on)).
rewrite /f2 - cpow_pow (csquare_inf icq) => r7.
apply: (cleT r6); apply: (cprod_Mlele _ r7); fprops.
Qed. 


Lemma infinite_power5' n p m (x:=\aleph n) (y:= \aleph (n +o p)):
   ordinalp n -> natp p -> m <> \0o -> p <=c m ->
   y ^c m = (x ^c m) *c y.
Proof.
move => pa pN  pd pe.
case: (equal_or_not p \0c) => pz.
  have ix:= CIS_aleph pa.
  have le1:=(cpow_Mle1 (proj1 ix) pd).
  have ipo:= (cle_inf_inf ix le1).
  by rewrite /y pz (osum0r pa) -/x (cprod_inf le1 ipo (infinite_nz ix)).

have pb:= (OS_nat pN).
have cp:=(card_card (CS_nat pN)); rewrite - cp  in pe pN pz.
rewrite (infinite_power5 pa pb pd pe).
by rewrite (cpow_inf  (CIS_aleph (OS_sum2 pa pb))).
Qed.

Lemma infinite_power5'' n p m (x:=\aleph n) (y:= \aleph (n +o p)):
   ordinalp n -> natp p -> infinite_c m ->
   y ^c m = (x ^c m) *c y.
Proof.
move => pa pb pc.
move:(Nat_hi pb) => pd.
exact:(infinite_power5' pa pb (infinite_nz pc) (cle_fin_inf pd pc)).
Qed.

Lemma infinite_power6  p m (y:= \aleph p):
  ordinalp p -> m <> \0o -> cardinal p <=c m ->
   (infinite_c m \/ p <> \0o) ->
   y ^c m = (\2c ^c m) *c (y ^c (cardinal p)).
Proof.
move=> op mz cpm dc.
have cm := proj32 cpm.
move: (infinite_power5 OS0 op  mz cpm).
rewrite (osum0l op) -/y aleph0E; move => ->.
have pa:= CIS_omega.
have aux:=(infinite_ge2 pa).
case: (finite_or_infinite cm) => fm; last first.
   move/infinite_c_P2:(fm) => fm'.
   by rewrite (infinite_power1_a aux fm' fm).
case: dc => pz; first by case: (finite_not_infinite fm pz).
have mb: natp m by apply /NatP.
have mpb: natp (cardinal p) by apply (NS_le_nat cpm mb).
rewrite (cpow_inf pa mb mz).
have iy:= (CIS_aleph op).
rewrite (cpow_inf iy mpb (card_nonempty0 pz)).
have le1: omega0 <=c \aleph p.
  by rewrite - aleph0E; apply: aleph_le_lec; by apply: ole0x.
have le2: \2c ^c m <=c \aleph p.
  apply: cleT le1.
  apply: cle_fin_inf => //;apply /NatP; apply: NS_pow; fprops.
rewrite cprodC (cprod_inf le1 iy omega_nz).
by rewrite cprodC (cprod_inf le2 iy (@cpow2_nz m)).
Qed.

Lemma infinite_power6_0  p m (y:= \aleph p): 
  ordinalp p -> infinite_c m -> cardinal p <=c m ->
   y ^c m = (\2c ^c m) *c (y ^c (cardinal p)).
Proof.
move=> op icm cp.
exact: (infinite_power6 op (infinite_nz icm) cp (or_introl icm)).
Qed.

Lemma infinite_power6_ct  p m (y:= \aleph p): 
  ordinalp p -> infinite_c m -> cardinal p <=c omega0  ->
   y ^c m = (\2c ^c m) *c (y ^c aleph0).
Proof.
move => ha hb hc.
move /infinite_c_P2: (hb) => hb'; move: (cleT hc hb') => hd.
rewrite (infinite_power6_0 ha hb hd).
case: (cle_eqVlt hc); first by move ->.
case: (equal_or_not p \0c) => epz.
  have he:= (infinite_pow2 hb).
    rewrite /y epz cardinal_set0 cpowx0 /aleph0 aleph0E (cprod1r (proj1 he)).
  by rewrite(infinite_power1_b CIS_omega) - cpow_sum2 csum_inf.
move/clt_omegaP => nn.
have pN: natp p by apply/NatP;apply:(ordinal_finite1 ha); apply/NatP.
rewrite (cpow_inf (CIS_aleph ha) nn (card_nonempty0 epz)).
by rewrite (infinite_power3 pN omega_nz) cprodA - cpow_sum2 (csum_inf hb' hb). 
Qed.

Lemma infinite_power5_ex:
  \aleph (omega1 +o omega0) ^c (\aleph \2o) =
  (\2c ^c  (\aleph \2o)) *c ((\aleph omega1) ^c aleph1) 
   *c (\aleph (omega1 +o omega0) ^c aleph0).
Proof.
have ha:= OS_aleph OS1.
have hb:= OS_omega.
have hc:= (CIS_aleph OS2).
have hd:= (infinite_nz hc).
move: (aleph_le_lec (proj1 olt_02)).
rewrite aleph0E /aleph0 -{1 4} (card_card CS_omega) => he.
have hi:= (card_card(CS_aleph OS1)).
move: (aleph_le_lec (proj1 olt_12)); rewrite - hi => hf.
by rewrite (infinite_power5 ha hb hd he) (infinite_power6_0 ha hc hf) hi.
Qed.

Lemma infinite_power6_1 a: a <o omega1 ->
  (\aleph a) ^c aleph1 = 
  (\aleph a) ^c aleph0 *c \2c  ^c aleph1.
Proof.
move => ao.
have oa:= proj31_1 ao.
have ica:=(CIS_aleph OS1).
move: ao => /(ocle2P (proj1 ica) oa) ao.
rewrite /aleph0 - aleph0E.
move: (aleph_nz oa) => xnz.
apply: cleA.
   rewrite (infinite_power6_0 oa ica (proj1 ao)) cprodC.
   apply: cprod_Mlele; last by apply: cleR; fprops.
   by apply: cpow_Meqle => //;apply: (aleph_pr10a OS0); rewrite osucc_zero.
have ioa:= (CIS_aleph oa).
apply: cprod_inf4.
- apply: cpow_Meqle => //; apply: aleph_le_lec; apply: ole0x; fprops.
- apply: cpow_Mleeq; [ apply: cle_fin_inf | ]; fprops.
- apply: CIS_pow => //; apply: aleph_nz; fprops.
Qed.

Lemma infinite_power6_2 b: b <o omega2 ->
  (\aleph b) ^c aleph2 = 
  (\aleph b) ^c aleph1 *c \2c  ^c aleph2.
Proof.
move => ao.
have oa:= proj31_1 ao.
have coo: cardinalp aleph2 by apply: CS_aleph; fprops.
move: ao => /(ocle2P coo oa) ao.
have xnz:= (aleph_nz oa).
apply: cleA.
   rewrite (infinite_power6_0 oa (CIS_aleph OS2) (proj1 ao)) cprodC.
   apply: cprod_Mlele; last by apply: cleR; fprops.
   by apply: cpow_Meqle => //;apply: (aleph_pr10a OS1); rewrite osucc_one.
have ioa:= (CIS_aleph oa).
apply: cprod_inf4.
- apply: cpow_Meqle => //;apply: aleph_le_lec;apply: oge1; fprops.
- apply: cpow_Mleeq; [ apply: cle_fin_inf |];fprops.
- apply: CIS_pow => //; apply: aleph_nz; fprops.
Qed.

Lemma infinite_power6_3:
  (\aleph omega0) ^c aleph1 = 
  (\aleph omega0) ^c aleph0 *c \2c  ^c aleph1.
Proof.
apply: infinite_power6_1.
rewrite - aleph0E; apply: aleph_lt_lto; apply: olt_01.
Qed.

Lemma infinite_power6_4 a b:
  infinite_o a -> a <o omega1 -> ordinalp b ->
  (\aleph a) ^c (\aleph b) = 
  (\aleph a) ^c aleph0 *c \2c  ^c (\aleph b).
Proof.
move => ioa a1 ob.
have oa:= proj31_1 a1.
have iob:= (CIS_aleph ob).
have eq1: cardinal a = \omega \0o.
  apply:cleA.
    apply/(aleph_pr10a OS0); rewrite osucc_zero.
    by move /(ocle2P (CS_aleph OS1) oa): a1.
  move:(infinite_set_pr2 ioa (ordinal_irreflexive oa)).
  rewrite  aleph0E;apply/infinite_greater_countable1.
move:(aleph_le_lec (ole0x ob)); rewrite - eq1 => ca2.
by rewrite (infinite_power6_0 oa iob ca2) cprodC eq1 aleph0E.
Qed.


Lemma infinite_power6_5 a b c : 
  ordinalp a -> ordinalp b ->
  \aleph (\omega a) = c ^c (\aleph b)  ->
  b <o a.
Proof.
move => oa ob.
have la:=(aleph_limit oa).
have aux: infinite_c (\aleph (\aleph a)).
  by apply: CIS_aleph;  apply: OS_aleph.
rewrite -(cpowcl c (\omega b)).
set C := cardinal c.
case: (equal_or_not C \1c) => eq1.
  rewrite eq1 cpow1x =>h;  move: aux; rewrite h; move: finite_1 => pa pb.
  case: (finite_not_infinite pa pb).
case: (equal_or_not C \0c) => eq0.
  by rewrite eq0 (cpow0x (aleph_nz ob)) => h;case:(infinite_nz aux).
move: (cge2 (CS_cardinal c) eq0 eq1) => c2 h.
move: (power_cofinality5 c2 (CIS_aleph ob)).
rewrite - (f_equal cofinality h) regular_initial_limit1 //.
move: (CIS_aleph oa) => ia.
move: (cofinality_small ia) => l1 l2.
exact: (aleph_ltc_lt ob oa (clt_leT l2 l1)).
Qed.

Lemma infinite_power6_6 n : ordinalp n ->
 \2c ^c (\aleph omega0) = \aleph (\omega n) -> omega0 <o n.
Proof.
move => on h3; symmetry in h3.
exact (infinite_power6_5 on OS_omega h3).
Qed.

Lemma infinite_power6_5a a b : infinite_c b ->
 \aleph omega1 = a ^c b  -> b  = aleph0.
Proof.
move => /ord_index_pr1; set n := ord_index b;move => [on <-] eq.
by move:(infinite_power6_5  OS1 on eq) => /olt1 ->; rewrite aleph0E.
Qed.

Definition gimel_fct x := x ^c (\cf x).

Lemma gimel_prop1 x: regular_cardinal x -> 
  gimel_fct x = \2c ^c x.
Proof.
by move=> /regular_cardinalP[ic xc]; rewrite /gimel_fct xc infinite_power1_b.
Qed.

Lemma gimel_prop2 x: infinite_c x -> 
  gimel_fct x <=c \2c ^c x.
Proof. 
move=> ic; rewrite /gimel_fct - (infinite_power1_b ic).
move: (cofinality_small ic) => cg.
apply: cpow_Mlele => //; [ by apply: infinite_nz | apply: (cleR (proj1 ic))].
Qed.


Lemma infinite_power6_7a: \2c ^c aleph1 = aleph2 ->
 \aleph omega0 ^c aleph1 = \aleph omega0 ^c aleph0.
Proof.
move => pa; move: infinite_power6_3; rewrite pa.
have pc: aleph2 <=c \aleph omega0 ^c aleph0.
  have l1:= (aleph_le_lec ole_2omega).
  apply: (cleT l1 (cpow_Mle1 (proj32 l1) omega_nz)).
have i2:=(CIS_aleph OS2).
have i3:= (cle_inf_inf i2 pc).
by rewrite (cprod_inf pc i3 (infinite_nz i2)).
Qed.

Lemma infinite_power6_7b:
  \2c ^c aleph1 = aleph2 ->
  (\aleph omega0) ^c aleph0 <> \aleph omega1.
Proof.
move => pa pb.
move: (esym (infinite_power6_7a pa)); rewrite pb => aux.
by case: (proj2(infinite_power6_5 OS1 OS1 aux)).
Qed.


Lemma infinite_power6_7c:
  \2c ^c aleph1 = aleph2 ->
  \aleph omega1 <c (\aleph omega0) ^c aleph0 ->
  \aleph omega1 ^c aleph1   = (\aleph omega0) ^c aleph0.
Proof.
set x1 := \aleph omega1.
set x2 := \aleph omega0 ^c aleph0.
move => pa [pb _].
have pc:= (aleph_nz OS_omega).
have x1nz := (aleph_nz (OS_aleph OS1)).
move: (aleph_le_lec ole_01); rewrite  aleph0E => pd.
have pe:= (aleph_le_lec (ocle pd)).
have pf := (cpow_Mleeq aleph0 pe pc). 
symmetry;apply: cleA.
  apply: (cleT pf); apply: cpow_Meqle => //; apply: aleph_nz.
have:  x1 ^c \aleph \1o  <=c x2 ^c \aleph \1o by apply: cpow_Mleeq.
move:  (infinite_power6_7a pa); rewrite -/x2 ; move => <-.
rewrite - cpow_pow csquare_inf //;apply: CIS_aleph; fprops.
Qed.

Lemma infinite_power6_7d:
  \aleph omega0 <c \2c ^c omega0 ->
  (\aleph omega0) ^c omega0 = \2c ^c omega0.
Proof.
move=> [h _ ].
move: (CIS_aleph OS_omega) => io.
apply: cleA; last first.
  apply cpow_Mleeq;[ by apply: infinite_ge2 | fprops].
move: (cpow_Mleeq omega0 h (infinite_nz io)).
rewrite - cpow_pow csquare_inf //; apply: CIS_omega.
Qed.

Lemma infinite_power6_7e:
   \aleph omega1  <=c \2c ^c omega0 ->
   (gimel_fct (\aleph omega0) = \2c ^c aleph0
   /\ gimel_fct (\aleph omega1) = \2c ^c aleph1).
Proof.
set o1 := \aleph \1o.
move => h;  rewrite /gimel_fct.
have h1: \aleph omega0 <=c \aleph o1. 
   rewrite - aleph0E; apply: aleph_le_lec; apply: (aleph_le_leo ole_01).
move: (cleT h1 h) => h2.
move: (regular_initial_limit1 (aleph_limit OS0)); rewrite aleph0E.
move: (regular_initial_limit1 (aleph_limit OS1)); rewrite -/o1.
move => -> ->.
have pa:= (CIS_aleph OS_omega).
rewrite (proj2 regular_omega).
move: (regular_cardinal_aleph1) => [pb].
rewrite (cofinality_card pb) -/o1; move => ->.
have cn2:=card2_nz.
split.
   apply: cleA.
     move: (cpow_Mleeq omega0 h2 (infinite_nz pa)).
     rewrite - cpow_pow csquare_inf //; apply: CIS_omega.
   apply: cpow_Mleeq => //; apply: cle_fin_inf => //; fprops.
move: (CIS_aleph (proj1 (proj1 pb))); rewrite -/o1 => io1.
have aux: (omega0 *c o1) = o1.
   rewrite cprodC; apply: (cprod_inf _ pb omega_nz).
   rewrite - aleph0E; exact (aleph_le_lec ole_01).
apply: cleA.
  move: (cpow_Mleeq o1 h (infinite_nz io1)). 
  by rewrite - cpow_pow aux.
exact: (cpow_Mleeq _ (infinite_ge2 io1) cn2).
Qed.

Lemma infinite_power6_7f:
  \aleph omega0 <c  (\aleph omega0) ^c aleph0 /\
  \aleph omega1 <c  (\aleph omega1) ^c aleph1.
Proof.
set x := \aleph omega0.
set y := \aleph omega1.
have icx: infinite_c x by apply: CIS_aleph; apply: OS_omega.
have icy: infinite_c y by apply: CIS_aleph; apply: OS_aleph; fprops.
have la: limit_ordinal omega1 by apply: aleph_limit; fprops.
split.
  move: (power_cofinality1 icx).
  by rewrite (regular_initial_limit1 omega_limit)  (proj2 (regular_omega)). 
move: (power_cofinality1 icy).
move: (regular_cardinal_aleph1)=> [pa <-].
by rewrite (cofinality_card pa)(regular_initial_limit1 la).
Qed.

Lemma ord_sup_aleph x: limit_ordinal x ->
  \csup (range (Lg x \aleph)) = \aleph x.
Proof.
by move => lx; rewrite ((proj2 aleph_normal) _ lx) Lg_range.
Qed.

Lemma infinite_increasing_power1 X b: 
  ofg_Mle_leo X -> domain X = \omega b -> ordinalp b ->
  cprod (Lg (domain X) (fun z => \aleph (Vg X z))) =
  \aleph (\osup (range X)) ^c \aleph b.
Proof.
move => px dx ob.
set Y := Lg _ _.
have p1: fgraph Y by rewrite /Y; fprops.
have dY: domain Y = \aleph b by rewrite /Y Lgd dx.
have p2: infinite_c (domain Y) by rewrite dY; apply CIS_aleph.
move: px => [fgx pa xi].
have nedx: nonempty (domain X).
  exists \0c; rewrite dx - dY; apply:(omega_limit3 p2); exact:NS0.
have p3: cardinal_pos_fam Y.
  by rewrite /Y; hnf;aw => a adx; rewrite LgV//; apply: aleph_nz1;apply: pa.
have p4: fg_Mle_lec Y.
  hnf; rewrite /Y; aw => u v ud vd uv; rewrite !LgV//; apply: aleph_le_lec.
  apply: (xi _ _ ud vd uv).
rewrite (infinite_increasing_power p1 p2 p3 p4).
by rewrite (sup_range_aleph fgx pa nedx) dY.
Qed.


Lemma infinite_increasing_power2 X b: 
  ofg_Mlt_lto X -> domain X = \omega b -> ordinalp b -> 
  cprod (Lg (domain X) (fun z => \aleph (Vg X z))) =
  \aleph (\osup (range X)) ^c \aleph b.
Proof.
move=> p1 p3 p4.
have lb: limit_ordinal (domain X) by rewrite p3; apply: aleph_limit.
move: ( ofg_Mlt_lto_p3 p1 lb) => p2.
by apply: infinite_increasing_power1.
Qed.

Lemma ord_sup_aleph_sum x: ordinalp x ->
  \csup (range (Lg omega0 (fun z=> \aleph (x +o z)))) =
    \aleph (x +o omega0).
Proof.
move => ox.
move: (normal_ofs_compose aleph_normal (osum_normal ox)) => [_ xb].
by move: (xb _ omega_limit) => /= ->; rewrite Lg_range.
Qed.

Lemma cprod_inf_eq x y i:
   fgraph x -> fgraph y -> (domain x = domain y) ->
   inc i (domain x) ->  (Vg x i) <> \0c -> Vg y i <> \0c -> 
   (exists j, [/\ inc j (domain x), j <> i, infinite_c (Vg x j),
     Vg x i <=c Vg x j & Vg y i <=c Vg x j]) ->
   (forall j, inc j (domain x) -> j = i \/ Vg x j = Vg y j) ->
  cprod x = cprod y.
Proof.
move => pa pb pc pd pe pf [j [qa qb qc qd qe]] ph.
set x' := Lg (domain x) (fun z => Yo (z = i) (Vg x j) (Vg x z)).
set y' := Lg (domain y) (fun z => Yo (z = i) (Vg y j) (Vg y z)).
have svj: Vg x j = Vg y j by case: (ph _ qa) => // aux; by case: qb.
have sp: x' = y'.
  rewrite /x' /y' -pc; apply: Lg_exten => k kdx; aw; Ytac xeq; Ytac0 => //. 
  case: (ph _ kdx) => // aux. 
suff: forall z, fgraph z ->  inc i (domain z) -> Vg z i <> \0c ->
    inc j (domain z) -> j <> i -> infinite_c (Vg z j) -> Vg z i <=c Vg z j ->
  cprod z = cprod (Lg (domain z)(fun t => Yo (t = i)(Vg z j) (Vg z t))).
  move => aux.
  rewrite (aux x pa pd pe qa qb qc qd) -/ x'.
  rewrite pc in pd qa; rewrite svj in qc qe.
  by rewrite (aux y pb pd pf qa qb qc qe) -/ y' sp.
move => z fgz idz jdz znz jni iv jv.
set z1 := (Lg (domain z) (fun t => Yo (t = i) (Vg z j) (Vg z t))).
move: (setC1_K idz); set j1 := (domain z) -s1 i => pA.
symmetry in pA.
have aux1: ~ inc i j1 by move /setC_P => [_] /set1_P; case.
rewrite (induction_prod1 pA aux1).
have fgz1: fgraph z1 by rewrite /z1; fprops.
have pN: domain z1 = j1 +s1 i by rewrite /z1; aw.
rewrite (induction_prod1 pN aux1).
have fg2: fgraph  (restr z j1) by fprops.
have fg3: fgraph  (restr z1 j1) by fprops.
have pC: sub j1 (domain z)  by move => t /setC1_P [].
have pD: sub j1 (domain z1) by rewrite /z1; aw.
have jj: inc j j1 by apply /setC1_P; split => //.
have dr1: (domain  (restr z j1))  = j1 by aw.
have dr2: (domain  (restr z1 j1))  = j1 by aw.
have jdz1: inc j (domain  (restr z j1)) by ue.
move: (setC1_K jdz1); set j2 :=  _ -s1  j => pE.
symmetry in pE.
have aux2: ~ inc j j2 by move /setC1_P=> [_].
rewrite (induction_prod1 pE aux2).
rewrite dr1 -dr2 in pE.
rewrite (induction_prod1 pE aux2)  - cprodA - cprodA.
have sc: sub j2 j1 by move => t  /setC1_P []; rewrite dr1.
move: (sub_trans sc pC) => sd.
rewrite (double_restr _ sc) (double_restr _ sc). 
rewrite /z1 !LgV//; Ytac0; Ytac0; apply:f_equal2.
  apply:f_equal; apply: fgraph_exten; aww.
   move=> k kj2. 
   have k2: inc k (domain z) by apply: sd.
   by rewrite !LgV//;Ytac ki; [ move: (sc _ kj2); rewrite ki |].
by rewrite (cprod_inf jv iv jdz) (csquare_inf iv).
Qed.

Lemma infinite_prod_pA:
  cprodb Nat csucc = cprodb Nat (fun z => (csucc (csucc z))).
Proof.
set j := Nat -s1 \0c.
set f := (Lg Nat csucc). 
have fgf: fgraph f by rewrite /f; fprops.
have sj:sub j (domain f) by rewrite /f; aw;apply sub_setC.
have sj1: sub (singleton \0c) Nat by move=> t /set1_P ->; apply:NS0.
have f1: (forall i, inc i ((domain f) -s j) -> (Vg f i) = \1c).
  rewrite /f/j; aw => i /setC_P [iN] /setC_P nv; rewrite LgV//.
  rewrite - succ_zero; ex_middle aux; case: nv;split => //. 
  by dneg i0; move /set1_P: i0 => ->.
rewrite /cprodb (cprod_one_unit sj f1).
have ->: cprodb j (Vg f) = cprodb j csucc.
  by rewrite /f;apply: cprodb_exten => i ii; rewrite LgV//; move/setC1_P: ii => [].
apply:cprod_Cn2; split => //.
+ move => t tN; apply /setC_P;split; first by apply:NS_succ.
  move /set1_P; apply: succ_nz.
+ move => u v uN vN;apply: csucc_inj; fprops.
+ move => y /setC1_P [yn ynz].
  by move: (cpred_pr yn ynz) => [pa pb]; exists (cpred y).
Qed.

Lemma infinite_prod_pB: cprodb Nat csucc = \2c ^c omega0.
Proof.
move:CIS_omega => io.
apply: cleA.
  rewrite - (infinite_power1_b io).
  rewrite - cprod_of_same.
  apply: cprod_increasing; aww.
  move=> x xN; rewrite !LgV//; apply:cle_fin_inf => //.
  by apply /NatP; apply: NS_succ.
rewrite - cprod_of_same infinite_prod_pA.
apply: cprod_increasing; aww => x xN; rewrite !LgV//.
rewrite - succ_one - succ_zero.
apply:cleSS; apply: cleSS. apply:(cle0n xN).
Qed.

Lemma cprod_An1 a b f: ordinalp a -> ordinalp b ->
  cprodb (a +o b) f = 
  cprodb a f *c cprodb b (fun z => f (a +o z)).
Proof.
move => oa ob.
rewrite {1} /cprodb; set g := Lg (a +o b) f.
have fgg: fgraph g by rewrite /g; fprops.
have sab:= proj33 (osum_Mle0 oa ob). 
move: (is_partition_with_complement sab).
have -> : a +o b = domain g by rewrite /g; aw.
move=> pfa.
rewrite (cprod_An pfa).
rewrite /partition_with_complement Lgd//; symmetry; apply: cprod2_pr.
set ff := fun l: Set => _.
have ->: cprodb a f = ff C0.
  rewrite /ff /g; aw ;apply: cprodb_exten  => s sf /=.
  by rewrite LgV//;apply: sab.
suff: (cprodb b (fun z => f (a +o z))) = ff C1
   by move => ->; apply doubleton_fam_canon.
rewrite /ff /g;aw. 
have -> : cprodb ((a +o b) -s a)(Vg (Lg (a +o b) f)) = cprodb ((a +o b) -s a) f.
   apply: cprodb_exten  => i /setC_P[ii _]; rewrite LgV//.
symmetry;apply:cprod_Cn2; split.
+ move => t tb; apply/setC_P; rewrite (osum_rec_def oa ob);split.
    apply /setU2_P; right; apply/funI_P; ex_tac.
  by move=> /(oltP oa) h1; move:(oltNge h1(osum_Mle0 oa (Os_ordinal ob tb))).
+ move => u v uo vo su. 
  move: (Os_ordinal ob uo) (Os_ordinal ob vo) => ou ov.
  exact (osum2_simpl ou ov oa su).
+ by rewrite (osum_rec_def oa ob); move => y /setC_P [/setU2_P] [] // /funI_P.
Qed.

Lemma infinite_prod_pB1: union (range (Lg Nat csucc)) = omega0.
Proof.
rewrite Lg_range; set_extens t.
  move => /setU_P [z tz /funI_P [u u1 uv]].
  rewrite uv in tz; exact:(NS_inc_nat (NS_succ u1) tz).
move => tu; apply/setU_P; exists (osucc t); fprops.
rewrite - (succ_of_nat tu); apply /funI_P; ex_tac.
Qed.

Lemma infinite_prod_pB2: (*alt proof *)
   cprodb Nat csucc = \2c ^c omega0.
Proof.
set x := (Lg Nat csucc).
have fgf: fgraph x by rewrite / x; fprops.
have icy: infinite_c (domain x) by rewrite /x; aw; apply: CIS_omega.
have pa: cardinal_pos_fam x.
  move;rewrite /x; aw; move=> a adx; rewrite /x LgV//;apply: succ_positive.
have pb:  fg_Mle_lec x. 
  move;rewrite /x; aw; move => a b aN bN [_ _ ab]; rewrite !LgV//.
  move:(CS_nat aN) (CS_nat bN) => ca cb.
  apply /(cleSSP ca cb); split => //.
rewrite /cprodb (infinite_increasing_power fgf icy pa pb).
rewrite /x infinite_prod_pB1; aw.
rewrite infinite_power1_b //;exact CIS_omega.
Qed.

Lemma infinite_prod_pC: 
   cprodb  Nat \aleph = (\aleph omega0) ^c omega0.
Proof.
set x := (Lg Nat \aleph).
have fgf: fgraph x by rewrite / x; fprops.
have icy: infinite_c (domain x) by rewrite /x; aw; apply: CIS_omega.
have pa:  cardinal_pos_fam x.
  move;rewrite /x; aw; move=> a adx; rewrite /x LgV//; apply: aleph_nz1.
  exact (OS_nat adx).
have pb:   fg_Mle_lec x. 
move;rewrite /x; aw; move => a b aB bB ab.
rewrite  !LgV//;exact (aleph_le_lec  ab).
rewrite /cprodb (infinite_increasing_power fgf icy pa pb).
by rewrite /x  (ord_sup_aleph omega_limit); aw.
Qed.

Lemma infinite_prod_pD (o2 := omega0 +o omega0):
   cprodb o2 \aleph = (\aleph o2) ^c omega0.
Proof.
set oo := (\aleph o2).
move: OS_omega => ioo.
apply: cleA.
  have -> :  oo ^c omega0 =  oo ^c (omega0 +o omega0).
    by rewrite - cpowcr cardinal_omega2 cpowcr.
  have oo2: ordinalp o2 by apply: OS_sum2.
  rewrite - cprod_of_same /cst_graph; apply: cprod_increasing; aww.
  by move=> x xB; rewrite !LgV//; apply: aleph_le_lec; apply/(oleP oo2); apply:setU1_r.
set p1:= cprod (Lg omega0 (fun z => (\aleph (omega0 +o z)))).
set x := (Lg omega0 (fun z : Set => \aleph (omega0 +o z))).
have fgf: fgraph x by rewrite / x; fprops.
have icy: infinite_c (domain x) by rewrite /x; aw; apply: CIS_omega.
have pa: cardinal_pos_fam x.
  move;rewrite /x; aw; move=> a adx; rewrite /x LgV//; apply: aleph_nz1.
   by apply: OS_sum2 => //; apply(Os_ordinal ioo adx).
have pb: fg_Mle_lec x. 
  move;rewrite /x; aw; move => a b aB bB ab; rewrite !LgV//.
  exact (aleph_le_lec (osum_Meqle ab ioo)).
move: (infinite_increasing_power fgf icy pa pb).
have ->: union (range x) = oo by  apply: (ord_sup_aleph_sum ioo).
rewrite {2} /x; aw; move => <-.
move: (cprod_An1  \aleph ioo ioo) => ->.
have  fg1: fgraph (Lg omega0 \aleph) by fprops.
rewrite cprodC; apply: cprod_M1le; rewrite /cprod;fprops.
apply /cprod_nzP; hnf;aw => i id; rewrite LgV//; apply:(aleph_nz(Os_ordinal ioo id)).
Qed.

Lemma infinite_prod_pE (o2 := omega1 +o omega0):
   cprodb o2 \aleph = (\aleph o2) ^c aleph1.
Proof.
set o1 := \aleph \1o.
have ico:= CIS_omega.
have ioo:= OS_omega.
have oo1: ordinalp o1 by apply: OS_aleph; apply: OS1.
move: (CIS_aleph OS1) => io1.
move /infinite_c_P2: (io1) => io2.
have px: cprod (Lg o1 \aleph) = (\aleph o1 ^c o1) ^c omega0.
   rewrite - cpow_pow  (cprod_inf io2 io1 omega_nz) //.
   set x :=  (Lg o1 \aleph).
   have qa:  (fgraph x)  by rewrite /x; fprops.
   have qb: (infinite_c (domain x)) by rewrite /x; aw.
   have qc: cardinal_pos_fam x.
     move; rewrite /x; aw => a ao; rewrite LgV//; apply: (aleph_nz1 (Os_ordinal oo1 ao)).
   have qd: fg_Mle_lec x.
   move; rewrite /x; aw; move => a b ax bx ab; rewrite !LgV//.
     exact (aleph_le_lec ab).
  move: (infinite_increasing_power qa qb qc qd).
  by rewrite /x; rewrite (ord_sup_aleph (aleph_limit OS1)); aw.
have pa: cprod (Lg omega0 (fun z => (\aleph (o1 +o z)))) =
   (\aleph o2) ^c omega0.
   set x := (Lg omega0 (fun z => (\aleph (o1 +o z)))).
   have qa:  (fgraph x)  by rewrite /x; fprops.
   have qb: (infinite_c (domain x)) by rewrite /x; aw.
   have qc: cardinal_pos_fam x.
     move; rewrite /x; aw => a ao; rewrite LgV//; apply: aleph_nz1.
     by apply: OS_sum2 => //; apply (Os_ordinal ioo ao).
   have qd: fg_Mle_lec x.
     move;rewrite /x; aw; move => a b ax bx ab; rewrite !LgV//.
     exact (aleph_le_lec (osum_Meqle ab oo1)).
  move: (infinite_increasing_power qa qb qc qd).
  by rewrite /x; move => ->; aw;  rewrite (ord_sup_aleph_sum oo1).
have <- : cprod  (Lg omega0 (fun z => (\aleph (o1 +o z) ^c o1)))
     = \aleph o2 ^c o1.
  move: pa; set f:= Lg omega0 _.
  have pb:  fgraph f by rewrite /f; fprops.
  move: (cpow_prod o1 f); rewrite /cprodb.
  have -> :  (Lg (domain f) (fun i => Vg f i ^c o1)) = 
    (Lg omega0 (fun z => \aleph (o1 +o z) ^c o1)).
    rewrite /f; aw; apply: Lg_exten => t te;rewrite LgV//.
  move => <- ->.
  rewrite - cpow_pow cprodC (cprod_inf io2 io1 omega_nz) //.
suff: cprodb omega0 (fun z => \aleph (o1 +o z) ^c o1) =
  cprodb omega0 (fun z => \aleph o1 ^c o1 *c \aleph (o1 +o z)).
  rewrite -/(cprodb omega0 _); move => ->.
  by rewrite - prod_of_prods (cprod_An1 \aleph oo1 ioo) cprod_of_same/cprodb px.
rewrite /cprodb;set l1:= Lg _ _; set l2 := Lg _ _.
have la: fgraph l1 by rewrite /l1; fprops.
have lb: fgraph l2 by rewrite /l2; fprops.
have lc: (domain l1 = domain l2) by rewrite /l1 /l2; aw.
have ld: inc \0o (domain l1) by rewrite /l1; aw; apply /NatP; fprops.
have oz: inc \0c omega0 by apply:NS0.
have aux1: \aleph o1 ^c o1 <> \0c.
     apply: infinite_nz; apply: CIS_pow2; apply: CIS_aleph; fprops.
have le: (Vg l1 \0c) <> \0c by rewrite /l1 LgV// (osum0r oo1).
have lf: (Vg l2 \0c) <> \0c.
  rewrite /l2 LgV//.
  by rewrite (osum0r oo1); apply: cprod2_nz => //; apply: aleph_nz.
have lg: (exists j, [/\ inc j (domain l1), j <> \0c, infinite_c (Vg l1 j),
     Vg l1 \0o <=c Vg l1 j & Vg l2 \0o <=c Vg l1 j]).
  have oo: inc \1o omega0 by apply:NS1.
  have d1: domain l1 = omega0 by rewrite /l1; aw.
  have i1d: inc \1o (domain l1) by ue.
  have le1: \aleph (o1 +o \0o) <=c \aleph (o1 +o \1o).
    apply: aleph_le_lec;apply: (osum_Meqle ole_01 oo1).
  exists \1o; split => //.
  - fprops.
  - rewrite /l1 LgV//; apply: CIS_pow2; apply: CIS_aleph; fprops.
  - rewrite /l1 ! LgV//; apply: cpow_Mleeq => //.
    apply: aleph_nz; apply: OS_sum2; fprops.
  rewrite /l1/l2  ! LgV// (osum0r oo1).
  set w :=  \aleph (o1 +o \1o) ^c o1.
  have sa: \aleph o1 <> \0c by apply: aleph_nz; fprops.
  have sb: \aleph o1 ^c o1 <=c w.
      apply: cpow_Mleeq => //; apply: aleph_le_lec.
      apply: osum_Mle0; fprops.
  have sc:  \aleph o1 <=c \aleph o1 ^c o1.
     have co1: cardinalp (\aleph o1) by apply CS_aleph.
     apply: cpow_Mle1 => //;apply: aleph_nz => //; fprops.
  move: (cle_inf_inf (CIS_aleph oo1) sc) => i2.
  exact: (cleT (cprod_inf1 sc i2) sb).
have lh:  (forall j, inc j (domain l1) -> j = \0o \/ Vg l1 j = Vg l2 j).
  rewrite /l1 /l2; aw;move => j jb.
  case: (equal_or_not j \0o) => jnz;[by left |  right; rewrite !LgV//].
  move: (card_nat jb) => pd.
  have pb: \aleph \1o <> \0o by apply: aleph_nz; fprops.
  have pc: cardinal j <=c \aleph \1o.
    rewrite pd; apply: (cleT _ io2).
    by apply: cle_fin_inf => //; apply /NatP.
  have pe:=(CIS_aleph (OS_sum2 oo1 (OS_nat jb))).
  move: (infinite_power5 oo1 (Os_ordinal ioo jb) pb pc).
  rewrite cpowcr.
  by rewrite - /omega1 -/o1 (cpow_inf pe jb jnz).
by rewrite (cprod_inf_eq la lb lc ld le lf lg lh).
Qed.



Lemma infinite_prod3 X c  (Y:= Lg (domain X) (fun z => \aleph (Vg X z)))
   (b:= omega0 ^o c):
   \0o <o c ->  ofg_Mlt_lto X -> domain X = b ->
  (cprod Y) = (\csup (range Y)) ^c (cardinal b).
Proof.
move => cp ax db.
have oc:= proj32_1 cp.
have lb: limit_ordinal b by apply: indecomp_limit2.
move: (lb); rewrite -db => lb1.
move: (increasing_sup_limit4 ax lb1) (aleph_sum_pr6 ax lb1);  rewrite -/Y.
set a := \osup (range X); move=> [la sra sav] pa.
move: ax => [gx ofx si]; rewrite sav.
apply: cleA; first by apply : infinite_increasing_power_bound1.
have pb:  \aleph a  <=c cprod Y.
   rewrite pa;apply:compare_sum_prod1 => //; rewrite /allf/Y; fprops.
   by aw; move=> i idx; rewrite LgV//; apply:infinite_ge2; apply: CIS_aleph;apply: ofx.
move: (cpow_Mleeq (cardinal b) pb (aleph_nz (proj31 la))).
rewrite db;move => h; apply:  (cleT h); clear pa pb h.
have dY: domain Y = b by rewrite /Y; aw.
set f := Lg (coarse b) (fun z => Vg Y (P z)).
have df: domain f = (coarse b) by rewrite /f; aw.
have fgf: fgraph f by rewrite /f; fprops.
have fgY: fgraph Y by rewrite /Y; fprops.
have ->: cprod Y ^c cardinal b = cprod f.
  set g := Lg b (fun z => (singleton z) \times b).
  have pa: partition_w_fam g (domain f).
    split => //.
        rewrite /g; fprops.
      hnf;rewrite /g; aw;move => i j id jd; rewrite !LgV//.
      case: (equal_or_not i j) => ij; [ by left | right ].
      apply: disjoint_pr => u /setX_P [_ p1 _] /setX_P [_ p2 _].
      by case: ij; move: p1 p2 => /set1_P <- /set1_P <-.
    rewrite df /coarse /g; set_extens t.
      move /setUb_P; aw; move => [y yb]; rewrite LgV//; move => /setX_P [p1] /set1_P.
      move => p2 p3; apply /setX_P;split => //; ue.
     move => /setX_P [p1 p2 p3]; apply /setUb_P; aw; exists (P t) => //.
     rewrite LgV //;apply /setX_P;split;fprops.
  rewrite (cprod_An pa) (cpow_prod _ Y) dY /g; aw; congr cprod.
  apply: Lg_exten; move => x xb.
  set s:= ((singleton x) \times b).
  have xx: cardinal s = cardinal b.  
    symmetry; apply /card_eqP; apply: Eq_rindexed.
  rewrite - xx cpowcr - cprod_of_same; rewrite LgV//; apply: cprodb_exten.
  move => v vd; aw; rewrite /f LgV//.
    by move: vd => /setX_P [_ /set1_P -> _].
  move:vd => /setX_P [p1 /set1_P p2 p3]; apply /setX_P;split => //; ue.
set g := Lg b (fun z => Zo (coarse b) (fun t => (P t)  +#o (Q t) =z)).
have pg: partition_w_fam g (domain f).
  split => //; rewrite /g /coarse/mutually_disjoint; aw.
  - fprops.
  - move => i j ib jb; case: (equal_or_not i j) => ij; [ by left | right ].
    rewrite !LgV//;apply: disjoint_pr => u /Zo_hi p1 /Zo_hi p2; case: ij. 
    by rewrite - p1 - p2.
  - rewrite df /coarse;set_extens t.
      by move /setUb_P; aw; move => [y yb]; rewrite LgV//; move => /Zo_P [].
    move: lb => [ob _ _] tb.
    move: (tb) => /setX_P [pt /(oltP ob) p1 /(oltP ob) p2]. 
    have pa: inc (natural_sum (P t) (Q t)) b.
      by apply /(oltP ob);  apply:natural_small.
    by apply /setUb_P; aw; ex_tac; rewrite LgV//;apply: Zo_i.
rewrite (cprod_An pg).
apply: cprod_increasing; [ by rewrite dY /g; aw | aw].
rewrite /g; aw => x xb; rewrite LgV//.
move: (natural_finite_cover oc xb).
rewrite - /b /coarse; set E:= Zo _ _; move => [pa pb].
have dr: domain (restr f E) = E.
  rewrite restr_d //; rewrite /E df; apply: Zo_S.
have xd: inc x (domain X) by ue.
have le1: forall i, inc i E -> Vg f i <=c Vg Y x.
  rewrite /f; move => i => /Zo_P [qa qb]; rewrite LgV//.
  move: qa => /setX_P [_ ipb iqb].
  have op:= (Os_ordinal (proj31 lb) ipb).
  have oq := (Os_ordinal (proj31 lb) iqb).
  move: (ord_compare_nat_sum1 op oq); rewrite qb.
  case: (equal_or_not (P i) x) => eq1.
    rewrite eq1 => _; apply: cleR; rewrite /Y LgV//; apply CIS_aleph.
    by apply: ofx.
   have pd: inc (P i) (domain X) by ue.
  move => eq2; move: (proj1 (si _ _ pd xd (conj eq2 eq1))) => le2.
  by rewrite /Y !LgV//; apply: aleph_le_lec.
have ix: infinite_c (Vg Y x).
  by rewrite /Y LgV//; apply: CIS_aleph; apply: ofx.
rewrite - (cpow_inf ix pa pb) cpowcr - cprod_of_same LgV //.
apply: cprod_increasing; aw; trivial => t tE.
by rewrite LgV// LgV//; apply: le1.
Qed. 

Lemma infinite_prod3_bis X m (Y:= Lg (domain X) (fun z => \aleph (Vg X z))):
  infinite_c m ->  ofg_Mlt_lto X -> domain X = m ->
  (cprod Y) = (\csup (range Y)) ^c m.
Proof.
move => im pa pb.
have idx:= (cardinal_indecomposable im).
have [y oy xv]:=(indecomp_prop3 idx).
case: (ozero_dichot oy) => ynz.
  by move: im; rewrite xv ynz oopow0=> /(finite_not_infinite finite_1).
rewrite xv in pb.
by rewrite (infinite_prod3 ynz pa pb) xv cpowcr.
Qed.

Lemma infinite_prod4 X a m
  (Y:= Lg (domain X) (fun z => \aleph (Vg X z) ^c m)):
  limit_ordinal a ->  \cf a <=c m -> domain X = \cf a ->
  ofg_Mlt_lto X -> a = \osup (range X) ->
  cprod Y = \aleph a ^c m.
Proof.
move => oa ca cdx ofx av.
have icc:=(cofinality_infinite_limit oa).
have im:= cle_inf_inf icc ca.
move:(cofinality_limit3 oa); rewrite - cdx => lc.
move: (infinite_prod3_bis icc ofx cdx).
move: (increasing_sup_limit4 ofx lc); rewrite -av; move => [pa _ ->] => pd.
move: (f_equal (fun z => z ^c m) pd).
rewrite - cpow_pow cpow_prod cprodC (cprod_inf ca im (infinite_nz icc)).
by move => <-; aw; rewrite /Y cdx; apply: cprodb_exten => x xd; rewrite LgV.
Qed.


Lemma infinite_prod44 X a b
  (Y:= Lg (domain X) (fun z => \aleph (Vg X z) ^c \aleph b)):
  limit_ordinal a -> \cf a <=o b -> domain X = \omega (\cf a) ->
  ofg_Mlt_lto X -> a = \osup (range X) ->
  cprod Y = \aleph a ^c (\aleph b).
Proof.
move => oa ca cdx ofx av.
have oc:=(OS_cofinality (proj31 oa)).
have icc:=(CIS_aleph oc).
have lc:= (infinite_card_limit2 icc).
move: (infinite_prod3_bis icc ofx cdx). 
rewrite - cdx in lc.
move:(increasing_sup_limit4 ofx lc); rewrite - av;  move => [pa _ ->] => pd.
move: (f_equal (fun z => z ^c \aleph b) pd).
rewrite - cpow_pow cpow_prod cprodC.
rewrite (cprod_inf (aleph_le_lec ca) (CIS_aleph (proj32 ca))(infinite_nz icc)).
by move => <-; aw; rewrite /Y cdx; apply: cprodb_exten => x xd; rewrite LgV.
Qed.



Lemma infinite_prod_pF:
   cprodb omega1 \aleph = (\aleph omega1) ^c aleph1.
Proof.
have ic: (infinite_c omega1) by apply CIS_aleph; fprops.
have oo:=(proj1 (proj1 ic)).
set (X :=  Lg omega1 id).
have sX: domain X = omega1 by rewrite /X; aw.
have ha: ofg_Mlt_lto X.
  have fhx: fgraph (Lg omega1 id) by fprops.
  rewrite /X;split => //;hnf;aw; [ move=> t to | move => u v uo vo uv];
    rewrite !LgV//; exact:(Os_ordinal oo to).
have sr: \osup (range X) = omega1.
  rewrite /X identity_r.
  by move :(limit_nonsucc (infinite_card_limit2 ic)).
have lo:limit_ordinal (domain X) by rewrite sX; exact:(aleph_limit OS1).
move: (infinite_prod3_bis ic ha sX).
move: (increasing_sup_limit4 ha lo) => [_ _ ->]; rewrite sr => <-.
by rewrite /X; aw; apply: cprodb_exten => x xa; rewrite LgV.
Qed.

Lemma infinite_prod_pG b: \1o <=o b ->
   cprodb omega1 (fun z => (\aleph z) ^c (\aleph b))
   = (\aleph omega1) ^c (\aleph b).
Proof.
move => b1.
have cp1: aleph1 <=c \aleph b by apply:aleph_le_lec b1.
have ie := CIS_aleph (proj32 b1).
move: (f_equal (fun z => z ^c \aleph b) infinite_prod_pF).
aw;rewrite cpow_prod - cpow_pow cprodC (cprod_inf cp1 ie (aleph_nz OS1)) => <-.
by aw;apply: cprodb_exten  => x xe; rewrite LgV.
Qed.


Lemma infinite_prod_pH b: ordinalp b ->
   cprodb omega0 (fun z => (\aleph z) ^c (\aleph b))
   = (\aleph omega0) ^c (\aleph b).
Proof.
move => ob.
have ie := CIS_aleph ob.
move/infinite_c_P2 : (ie) => iea.
move: (f_equal (fun z => z ^c \aleph b) infinite_prod_pC).
rewrite cpow_prod - cpow_pow cprodC (cprod_inf iea ie omega_nz) => <-.
by aw; apply: cprodb_exten => x xd; rewrite LgV.
Qed.

Lemma infinite_prod5 a:
  (limit_ordinal a) ->
  cprodb a \aleph = (\aleph a) ^c (cardinal a).
Proof.
move => la.
pose p j := limit_ordinal j -> 
  cprodb j \omega = \omega j ^c cardinal j.
apply: (least_ordinal2 (p:=p))  (proj31 la) la => y oy etc ly.
move: (cantor_of_limit ly) => [c [n [oc on nz yv cp]]].
have np := (ord_ne0_pos on nz).
have op:= (OS_pow OS_omega on). 
case: (equal_or_not c \0o) => cz.
  move: yv; rewrite cz (osum0l op) => yv.
  set X := (Lg y id).
  have dx: domain X = omega0 ^o n by rewrite -yv /X; aw.
  have osx: ofg_Mlt_lto X.
    rewrite /X /ofg_Mlt_lto /ordinal_fam;split;fprops.
    hnf; aw;move => x xy;rewrite LgV//; exact (Os_ordinal oy xy).
    hnf; aw;move => u v ux vx uv; rewrite !LgV//.
  move: (infinite_prod3 np osx dx).
  have ->: (Lg (domain X) (fun z => \omega (Vg X z))) = (Lg y \omega).
    rewrite /X; aw; apply: Lg_exten => t te; rewrite LgV//.
  by move => h; rewrite /cprodb h -yv  ord_sup_aleph.
case: cp => [ cnz // |[lc le1 sv]].
have cy: c <o y.
  by move: (osum_Meqlt (opow_pos olt_0omega on) oc); rewrite (osum0r oc) -yv.
move: (etc _ cy lc); rewrite - sv => eq1.
rewrite {1} yv (cprod_An1 \aleph oc op) eq1.
set X := Lg (omega0 ^o n) (fun z => (c +o z)).
have dx: domain X = omega0 ^o n by rewrite /X; aw.
have xx: ofg_Mlt_lto X.
  split; rewrite /X; fprops.
     hnf;aw; move => x xv; rewrite LgV//; exact:(OS_sum2 oc (Os_ordinal op xv)).
  hnf; aw; move => u v ud vd; rewrite !LgV// => lt1.
  by apply: osum_Meqlt.
move: (infinite_prod3 np xx dx); rewrite /cprodb.
set L1:= Lg _ _; set L2 := Lg _ _.
have ->: L1 = L2 by rewrite /L1 /L2 /X;aw; apply: Lg_exten => x xd; rewrite LgV//.
have l1: limit_ordinal (omega0 ^o n) by apply:indecomp_limit2.
have ->: union (range L2) = \omega y.
  move: (normal_ofs_compose  aleph_normal (osum_normal oc)) => [_ xb].
  by move: (xb _ l1); rewrite -/L2 /= yv; move => ->; rewrite /L2 Lg_range.
move => ->;clear L1 L2. 
have cnz: cardinal y <> \0c.
  by apply:card_nonempty1; move: ly => [_ ok _]; exists \0c.
have le2: cardinal (omega0 ^o n) <=c cardinal y.
  by apply ocle1; rewrite yv; apply: osum_M0le.
by move: (infinite_power5 oc op cnz le2); rewrite -yv => ->.
Qed.

Lemma infinite_prod6 a:
  ordinalp a -> a <> \0o -> 
  cprodb (osucc a) \aleph = (\aleph a) ^c (cardinal a).
Proof.
move => oa anz.
pose p j := j <> \0o -> 
  cprodb (osucc j) \omega = \omega j ^c cardinal j.
apply: (least_ordinal2 (p:= p)) oa anz => y oy lyp ynz.
have ->: cprodb (osucc y) \aleph = 
    (cprodb y \omega) *c (\aleph y).
  rewrite - (osucc_pr oy) (cprod_An1 \aleph oy OS1); congr (_ *c _).
  rewrite /cprodb;set f := Lg _ _.
  have fg: fgraph f by rewrite /f; fprops.
  have df: domain f = singleton \0o by rewrite /f; aw.
  have f0: Vg f \0o = \omega y. 
    rewrite /f LgV; [by rewrite (osum0r oy) | by apply /set1_P ].
    by rewrite (cprod_trivial1 df) card_card // f0; apply: CS_aleph. 
have cny: cardinal y <> \0c. 
    case: (emptyset_dichot y) => ey; first by contradiction.
    by apply card_nonempty1.
case: (ordinal_limA oy) => h; first contradiction; last first.
  have onz: \omega y <> \0c by apply: aleph_nz.
  have p1: \omega y <=c \omega y ^c cardinal y.
      apply: (cpow_Mle1 (CS_aleph oy)  cny).
  move: (cle_inf_inf (CIS_aleph oy) p1) => p2.
  by rewrite (infinite_prod5 h); apply: (cprod_inf).
move: h => [z oz zv].
case: (equal_or_not z \0o) => znz.
  rewrite zv znz osucc_zero /cprodb.
  set f := Lg _ _.
  have fg: fgraph f by rewrite /f; fprops.
  have df: domain f = singleton \0o by rewrite /f; aw.
  have f0: Vg f \0o = \omega \0o. 
    by rewrite /f LgV//; apply /set1_P.
  have cv: cardinalp (Vg f \0o) by rewrite  f0; apply: CS_aleph; fprops.
  rewrite (cprod_trivial1 df) f0 (card_card CS1) cprod2cl cprodC.
  have p1: \omega \0o <=c \omega \1o.
    by  apply: aleph_le_lec; apply: ole_01.
  by rewrite (cprod_inf p1 (CIS_aleph OS1) (aleph_nz OS0)) (cpowx1 (proj32 p1)).
have lt1:  z <o y by rewrite zv; apply: oltS.
rewrite zv in cny.  
rewrite zv (lyp _ lt1 znz) (infinite_power2 oz cny); apply: f_equal2;last exact.
case: (p_or_not_p (infinite_o z)) => zi.
  hnf in zi; have <- //: cardinal z = cardinal (osucc z).
  by apply /card_eqP.
have fz:finite_o z by split.
rewrite - (succ_of_finite fz).
have zN: natp z  by apply /NatP.
rewrite (card_nat zN) (card_card (CS_succ z)).
rewrite (cpow_succ _ zN).
symmetry.
have onz: \omega z <> \0c by apply: aleph_nz.
have p1: \omega z <=c \omega z ^c z.
    apply: (cpow_Mle1 (CS_aleph oz)  znz).
move: (cle_inf_inf (CIS_aleph oz) p1) => p2.
apply: (cprod_inf) => //.
Qed.

Lemma infinite_power7c x y:
  cardinalp x -> cardinalp y ->
  cardinal (unionb (Lg x (functions y)))
  <=c (csum (Lg (cardinals_lt x) (fun z => z ^c y))) *c x.
Proof. 
move => cx cy.
set g :=  Lg _ _.
have fg: fgraph g by rewrite /g; fprops.
apply: (cleT (csum_pr1 _)).
set f := (Lg x (fun z => cardinal z ^c y)).
have fgf: fgraph f by rewrite /f; fprops.
set h := Lg (cardinals_lt x) (fun i => Zo x (fun t => (cardinal t) = i)).
have fgh: fgraph h by rewrite /h; fprops.
have dh: domain h = (cardinals_lt x) by rewrite /h; aw.
have mh: mutually_disjoint h.
  by apply mutually_disjoint_prop2 => i j z id jd /Zo_hi => <- /Zo_hi <-.
move: (proj1 cx) => ox.
have ph: partition_w_fam h (domain f).
  split => //; rewrite /f;aw; set_extens t. 
     move /setUb_P => [z za];rewrite /h LgV ; [by move => /Zo_P [] | ue].
  move => tx; apply /setUb_P.
  have ot:= (Os_ordinal ox tx).
  have ts: inc (cardinal t) (cardinals_lt x).
    by apply /(cardinals_ltP cx); apply /(ocle2P cx ot); apply/oltP.
  exists (cardinal t); [by rewrite dh | by rewrite /h LgV//; apply: Zo_i].
rewrite /csumb;set u := csum _.
move: (csum_An ph).
have -> : u = csum f.
   rewrite /u /f; apply: f_equal; rewrite /g; aw; apply: Lg_exten=> t tx.
   by rewrite LgV// cpow_pr1 (card_card cy).
move ->.
rewrite -dh.
have fgfxx: fgraph (Lg (domain h) (cpow^~ y)) by fprops.
rewrite cprodC (cprod2Dn); aw.
apply: csum_increasing;aw; trivial.
move=> z zd; rewrite LgV//.
have pc: sub (Vg h z) (domain f).
  move: ph => [_ _ un]; rewrite -un.
  move=> t th; apply /setUb_P; exists z => //; ue.
have pd: sub (Vg h z) x by  move: pc; rewrite /f; aw.
have pb: domain (restr f (Vg h z)) = Vg h z by aw.
have ->: (csumb (Vg h z) (Vg f)) = csumb (Vg h z) (fun t => z ^c y).
  rewrite/f;apply:  csumb_exten => t td; move: (pd _ td) => tx; rewrite LgV//.
  move: td; rewrite /h LgV; [ move /Zo_P; move => [_ -> //] | ue].
rewrite  csum_of_same cprodC - cprod2cl LgV//.
apply cprod_Mlele.
  by move: (sub_smaller pd); rewrite (card_card cx).
apply: cleR; rewrite /cpow;fprops.
Qed.


Lemma infinite_power7d x (y := cardinal (cardinals_lt x)):
   cardinalp x -> x <> \0c -> 
   (y <=c x /\ y <> \0c).
Proof.
move=> cx xnz;rewrite -(card_card cx); split.
  apply:sub_smaller=> t /Zo_P [_ ok]; move: (oclt ok).
  by move =>/ oltP0  [_ _].
apply: card_nonempty1; exists \0c.
by apply /(cardinals_ltP cx); split; [apply: cle0x | apply:nesym ].
Qed.

Lemma infinite_power7 x y: 
  infinite_c x -> y <c \cf x -> y <> \0c ->
  x ^c y =  (csumb (cardinals_lt x) (fun z => z ^c y)) *c x.
Proof.
move=> pa pb pc.
have cy:= proj31_1 pb.
have cx:= proj1 pa.
have le1:= (infinite_power7b pa pb).
have le2:= (infinite_power7c cx cy).
apply: (cleA (cleT le1 le2)).
have pd:= (cpow_Mle1 cx pc).
have ip:=(cle_inf_inf pa pd).
apply: (cprod_inf4 _ pd ip).
set f := (Lg (cardinals_lt x) (cpow^~ y)).
have fl:  (forall i, inc i (domain f) -> Vg f i <=c x ^c y).
  rewrite /f; aw; move=> i id; rewrite LgV//.
  case: (equal_or_not i \0c) => iz.
     rewrite iz (cpow0x pc);apply: (cle0x (proj32 pd)).
  move: id => /(cardinals_ltP cx) [le _].
  by apply: cpow_Mleeq.
move: (infinite_power7d cx (infinite_nz pa)) => [pe1 pf].
have fgf: fgraph f by rewrite /f; fprops.
move: (csum_of_small_b1 (conj fgf fl)); rewrite {2}/f; aw.
rewrite - cprod2cr cprod_inf//; exact: (cleT pe1 pd).
Qed.

Lemma infinite_power7e a y: 
  limit_ordinal a -> y <> \0c ->
  \aleph a <=c \osup (fun_image a (fun z => (\aleph z) ^c y)). 
Proof.
move=> ln ynz.
move: aleph_normal => [qa qb]; rewrite (qb _ ln).
set T2:= fun_image _ _.
set T := fun_image _ _.
have csr: cardinal_set T by move=> t /funI_P [z zn ->]; fprops. 
apply:card_ub_sup; first by apply: (CS_sup csr).
move => // i /funI_P [z zn ->].
have sr1: inc ((\aleph z) ^c y) T by apply  /funI_P; ex_tac.
apply: cleT (card_sup_ub csr sr1).
have oz:= (Os_ordinal (proj31 ln) zn).
exact:(cpow_Mle1 (CS_aleph oz) ynz). 
Qed.

Lemma infinite_power7f a y: 
  limit_ordinal a -> y <c \cf a ->
  (\aleph a) ^c y = \osup (fun_image a (fun z => (\aleph z) ^c y)). 
Proof.
move => p1 p2.
have on:= (proj31 p1).
case: (equal_or_not y \0c) => yz.
  rewrite yz cpowx0; set T := fun_image _ _.
  suff: T = singleton \1c  by move => ->; rewrite setU_1.
  apply set1_pr.
    by move: p1 => [q1 q2 q3]; apply /funI_P; exists \0o => //; rewrite cpowx0.
  by move=> t /funI_P [z zn ->]; rewrite cpowx0.
move: (CIS_aleph on); set x:= \aleph a => icx.
rewrite - (regular_initial_limit1 p1) in p2.
have aux:= (infinite_power7 icx p2 yz).
set T := fun_image _ _.
set s := union T.
have s3: s <=c x ^c y.
   apply: card_ub_sup; first by fprops.
   move => i /funI_P [z zn ->].
   have [zn1 _]: z <o a by  apply /oltP.
   exact: cpow_Mleeq (aleph_le_lec zn1) (aleph_nz (proj31 zn1)).  
move: aux; set f := (Lg (cardinals_lt x) (cpow^~ y)) => aux.
have cff: cardinal_fam f by rewrite /f; hnf; aw; move=> i ad; rewrite LgV//; fprops.
have cx:= proj1 icx.
have cdf1: cardinal (domain f) <=c x.
  rewrite /f Lgd; exact (proj1 (infinite_power7d cx (infinite_nz icx))).
have fgf: fgraph f by rewrite /f; fprops.
have osr: ordinal_set (range f).
  move=> t /(range_gP fgf). rewrite /f;aw; move=> [z zv -> ]. 
  rewrite LgV//;apply: OS_cardinal; fprops.
have sr: s = \osup (range f).
  rewrite /s /T /f; apply: ord_sup_1cofinal => //; split.
    move=> t /funI_P [z zn ->]; apply /(range_gP fgf).
    have os: inc (\aleph z) (cardinals_lt x).
      by apply /(cardinals_ltP cx) /aleph_lt_ltc /oltP.
    rewrite /f; aw; exists (\aleph z) => //; rewrite LgV//.
  move=> i /(range_gP fgf); rewrite /f; aw; move=> [u us]; rewrite LgV// => ->.
  move: us => /(cardinals_ltP cx) us.
  have cu:= proj31_1 us.
  case: (finite_or_infinite cu) => fc.
     exists (omega0 ^c y) => //.
       apply /funI_P; exists \0o; [exact (proj32 p1) | by rewrite aleph0E ].
     apply: ocle.
     case: (equal_or_not u \0c) => uz.
       rewrite uz (cpow0x yz); apply: cle0x; rewrite /cpow;fprops.
     apply: cpow_Mleeq=> //;apply: cle_fin_inf => //.
     exact: (CIS_omega).
  move:(ord_index_pr1 fc) => [om uv].
  exists (u ^c y).
    apply /funI_P; exists (ord_index u); rewrite ? uv  => //. 
    apply /(oltP on); apply: aleph_ltc_lt => //; ue.
  exact: (ocle(cleR (CS_pow u y))).
move: (infinite_power7e p1 yz).
rewrite -/x -/T -/s => xs.
have pc: (infinite_c s) by apply: (cle_inf_inf icx xs).
have pd:= cleT cdf1 xs.
rewrite sr in pc pd xs.
move: (csum_of_small_b4 fgf cff pc pd);rewrite aux sr  /csumb -/f => ->.
by apply: cprod_inf => //;apply: infinite_nz.
Qed.


Lemma infinite_power7f1 a y: 
  limit_ordinal a -> y <c \cf a -> y <> \0c ->
  (\aleph a) ^c y = csumb a (fun z => (\aleph z) ^c y). 
Proof.
move => pa pb pc.
have on:= (proj31 pa).
move: (infinite_power7f pa pb); rewrite - Lg_range=> eq0.
move: (ocle1 (aleph_pr6 on)); rewrite (card_card (CS_aleph on)) => le2.
rewrite eq0;symmetry; apply: csum_of_small_b4. 
- fprops.
- by hnf; aw; move=> i an; rewrite LgV//; fprops.
- by rewrite - eq0;  apply: CIS_pow => //; apply: CIS_aleph.
- by rewrite - eq0 Lgd; exact: (cleT le2  (cpow_Mle1 (proj32 le2) pc)). 
Qed.

Lemma infinite_prod_pI:
  csumb omega1 (fun z => \aleph z ^c aleph0) = \aleph omega1 ^c aleph0.
Proof.
have la: limit_ordinal omega1 by apply: aleph_limit; fprops.
have ic: infinite_c omega1 by apply: CIS_aleph; fprops.
have cf:  omega0 <c cofinality aleph1.
    move: (proj2 (regular_cardinal_aleph1)). 
    rewrite (cofinality_card ic) => ->.
  rewrite - aleph0E; apply: aleph_lt_ltc; apply: olt_01.
rewrite (infinite_power7f1 la cf) //; first by apply: omega_nz.
Qed.

Lemma infinite_power8 n (x:= \aleph n) (z:= \cf x) y:
   ordinalp n -> z <=c y ->
   x ^c y = ( \osup (fun_image (cardinals_lt x) (fun t => t ^c y))) ^c z.
Proof.
move=> ln cy.
set T := fun_image _ _.
have cst: cardinal_set T. 
   move=> t /funI_P [zs _ ->]; rewrite /cpow; fprops. clear cst.
have icx: infinite_c x by apply: CIS_aleph.
have cxy: cardinalp (x ^c y) by rewrite /cpow; fprops.
have H:= (cofinality_card icx).
move: (cofinality_infinite icx); rewrite H -/z => icz.
have icy:= (cle_inf_inf icz cy).
have sx: \osup T <=c x ^c y.
  apply: card_ub_sup => //.
  move=> a /funI_P [u up ->].
  case: (equal_or_not u \0c) => uz.
    rewrite uz cpow0x; [by apply cle0x | by  apply: infinite_nz].
  apply: cpow_Mleeq => //.
  by move: up => /(cardinals_ltP (proj1 icx)) [].
apply: cleA; last first.
  have znz: z <> \0c by apply: infinite_nz.
  case: (equal_or_not (\osup T) \0c) => snz.
    by rewrite snz cpow0x => //; apply cle0x. 
  have : (\osup T) ^c z <=c   (x ^c y) ^c z by apply: cpow_Mleeq => //.
  rewrite - cpow_pow (cprod_inf cy) //.
move: (cofinality_c_pr3 icx) => [f [[[pc1 pc2 pd pe] pf] pc]].
have qa: x <=c cprod f.
   rewrite -pf; apply: compare_sum_prod1 => //.
have : x ^c y <=c (cprod f) ^c y.
   by apply: cpow_Mleeq => //;apply: infinite_nz.
rewrite (cpow_prod _ f) /cprodb.
set p := cprod _ => le1.
have cst: cardinal_set T by move=> t /funI_P [tt _ ->]; fprops.
have: p <=c cprodb  (domain f) (fun i => \osup T).
  apply: cprod_increasing; aw; trivial => t tdf; rewrite !LgV//.
  apply: card_sup_ub => //; apply /funI_P; exists (Vg f t) => //.
  by apply /(cardinals_ltP (proj1 icx));  apply: pd.
by rewrite cprod_of_same pe H; apply:cleT.
Qed.

Lemma infinite_power9 x y: infinite_c x -> infinite_c y ->
  [/\ (x <=c y ->  x ^c y = \2c ^c y),
      (forall  z, z <c x -> x <=c z ^c y -> x ^c y = z ^c y) &
     ((forall z,  z <c x -> z ^c  y <c x) ->
     ( ( y <c \cf x  -> x ^c y = x)
       /\ (\cf x <=c y -> x ^c y = x ^c (\cf x))))].
Proof.
move => icx icy.
have ynz:=(infinite_nz icy). 
have xnz:= (infinite_nz icx).
split.
    by move => h; apply: infinite_power1_a => //; apply: infinite_ge2.
  move=> z le1 le2; apply: cleA.
    rewrite - {2} (csquare_inf icy) cpow_pow. 
    by apply: cpow_Mleeq.
  have znz: z <> \0c.
    move=> bad; case: xnz; move: le2; rewrite bad cpow0x // => b1.
    apply (cle0 b1).
  apply: cpow_Mleeq => //; exact (proj1 le1).
move => h.
have x2: \2c <c x by apply: clt_fin_inf => //; apply /NatP; fprops.
have yx:= (cle_ltT (proj1 (cantor (proj1 icy))) (h _ x2)).
have [on xv]:= (ord_index_pr1 icx).
case: (ordinal_limA on) => nz.
    move: yx; have ->: x = omega0 by rewrite -xv nz aleph0E.
    by move: icy => /infinite_c_P2 icy /(cleNgt icy).
  move:nz=> [m om nv].
  move: (regular_initial_successor om) => /regular_cardinalP [_ ww].
  move: yx h; rewrite -xv nv ww => yo h;split; last by move=> /(cltNge yo).
  have le2 := (h _ (aleph_pr10c om)).
  move => _.
  move: (infinite_power2 om ynz).
  have pa: (infinite_c (\aleph (osucc m))) by apply: CIS_aleph; ue.
  have pb:=(cpow_nz (b := y) (aleph_nz om)).
  by rewrite cprodC (cprod_inf (proj1 le2) pa pb).
split.
  rewrite -xv  (regular_initial_limit1 nz) => yc.
  move: (infinite_power7e nz ynz).
  rewrite (infinite_power7f nz yc).
  set T := fun_image _ _; move=> le1.
  apply: cleA => //.
  apply: (card_ub_sup  (proj31 le1)).
  move => a /funI_P [z zn ->]; rewrite - xv in h.
  have aux : \aleph z <c \aleph (ord_index x).
    by apply: aleph_lt_ltc; move: zn =>/oltP [].
  apply: (proj1 (h _ aux)).
rewrite -xv; move=> cf1.
have oxne: \aleph (ord_index x) <> \0c by ue.
apply: cleA; last by apply: cpow_Meqle.
rewrite {1} (infinite_power8 on cf1); set T2:= fun_image _ _.
case: (equal_or_not (union T2) \0c) => unz.
  rewrite unz cpow0x; first by apply: cle0x; fprops.
  apply: infinite_nz; apply:cofinality_infinite_cardinal; ue.
apply: cpow_Mleeq => //.
apply: card_ub_sup; first by rewrite xv; exact (proj1 icx).
move=> a; rewrite /T2 xv => /funI_P [z zi ->].
move: zi => /(cardinals_ltP (proj1 icx)) zi.
exact: (proj1  (h _ zi)).
Qed.

Lemma infinite_power7g x y: infinite_c x -> x <=c y ->
  x ^c y =  (csumb (cardinals_lt x) (fun z => z ^c y)) *c x.
Proof.
move => icx xy.
have [cx cy _]:= xy.
have icy: infinite_c y by apply: (cle_inf_inf icx xy).
have ynz: y <> \0c by apply: infinite_nz.
have x2: \2c <=c x by apply: infinite_ge2.
rewrite (infinite_power1_a (infinite_ge2 icx)  xy icy) /csumb.
have pa:= cleT xy (proj1 (cantor cy)).
move: (infinite_power7d (proj1 icx) (infinite_nz icx)) => [pb pc].
set f := Lg _ _.
have cf: fgraph f by rewrite /f; fprops.
have pd: infinite_c (\2c ^c y) by apply: (cle_inf_inf icx pa).
have fl:  forall i, inc i (domain f) -> Vg f i <=c \2c ^c y.
  rewrite /f; aw; move=> i idf; rewrite LgV//.
  move: idf => /(cardinals_ltP cx) idf.
  have p1:= (proj1 (clt_leT idf xy)).
  case: (equal_or_not i \0c) => iz.
    rewrite iz (cpow0x ynz); apply: cle0x; fprops.
  case: (equal_or_not i \1c) => io.
    by rewrite io (cpow1x); apply: (cle_fin_inf finite_1).
  have i2:= (cge2 (proj31 p1) iz io).
  rewrite (infinite_power1_a i2 p1 icy).
  apply: cleR; rewrite /cpow; fprops.
move: (csum_of_small_b1 (conj cf fl)); rewrite {2} /f; aw.
rewrite - cprod2cr => le2.
have le3:= (cleT le2 (cprod_inf1 (cleT pb  pa) pd)).
apply:cleA; last by apply: cprod_inf4.
apply: cleT (cprod_M1le (proj31 le3) (infinite_nz icx)).
have d2: inc \2c (cardinals_lt x).
   apply/(cardinals_ltP cx). 
   apply: (clt_fin_inf finite_2 icx). 
move:(proj1 pd).
have ->:  \2c ^c y = Vg f \2c by rewrite /f LgV.
by move => cc;apply(csum_increasing6 cc); rewrite/f Lgd.
Qed.

Lemma infinite_power7h x y: 
  regular_cardinal x -> \0c <c y ->
  x ^c y =  (csumb (cardinals_lt x) (fun z => z ^c y)) *c x.
Proof.
move=> /regular_cardinalP [ic cfx] [[_ cy _] nzy].
case: (cleT_el (proj1 ic) cy) => xy; last first.
  rewrite - cfx in xy; exact: (infinite_power7 ic xy (nesym nzy)).
by apply: infinite_power7g.
Qed.

Lemma infinite_power6w y: infinite_c y ->
  ( (exists2 x, y <c x & x ^c y = x) /\
    (exists2 x, y <c x & x <c x ^c y)).
Proof.
move => h; split.
  exists (\2c ^c y); first by apply: (cantor (proj1 h)).
  rewrite - cpow_pow csquare_inf //.
move: (ord_index_pr1 h)=> [on yv].
move: (cnextE on); rewrite yv; set z:= cnext y => zv.
have yz: y <c z by rewrite -yv zv; apply: aleph_pr10c.
have oz:= (OS_cardinal (proj32_1 yz)).
have osn:= (OS_succ on).
have zp: \aleph z <> z.
  move=> eq; rewrite {2} zv in eq.
  move: (aleph_inj oz osn eq).
  move: (aleph_limit osn); rewrite - zv; move => [la lb lc] zs.
  have nz: inc (ord_index y) z by  rewrite zs /osucc; fprops.
  move: (lc _ nz); rewrite - zs => bad; exact (ordinal_irreflexive oz bad).
have tp:= (normal_ofs_fix aleph_normal oz).
have cft:= (cofinality_least_fp_normal aleph_normal zp tp).
move: tp =>[];  set t := the_least_fixedpoint_ge _ _  => tp1 tp2 tp3.
have cz: cardinalp z by rewrite zv; apply: CS_aleph.
have ct: cardinalp t by rewrite -tp2; apply: (CS_aleph (proj32 tp1)).
have yt: y <c t.
  apply: (clt_leT yz).
  rewrite - (card_card cz)  - (card_card ct).
  by apply: ocle1.
have ict: infinite_c t by apply: (cle_inf_inf h (proj1 yt)).
exists t => //.
apply: (clt_leT (power_cofinality (infinite_ge2 ict))).
apply: cpow_Mlele.
    by apply: infinite_nz.
  move: ict => [cat _]; fprops.
by rewrite (cofinality_card ict) cft; apply /infinite_c_P2.
Qed.

Definition cpow_less x y := 
  \csup (fun_image (cardinals_lt y) (fun t => x ^c t)).

Notation "x ^<c y" := (cpow_less x y) (at level 30).

Lemma cpow_less_pr0 x y: 
  cardinal_set (fun_image (cardinals_lt y) (fun t => x ^c t)).
Proof. move => t /funI_P [z _ ->]; fprops. Qed.

Lemma cpow_less_alt x y :
  infinite_c y -> \2c <=c x -> 
  x ^<c y = csumb (cardinals_lt y) (fun t => x ^c t). 
Proof.
move=> icy xy.
rewrite /cpow_less; set E :=  (cardinals_lt y).
set f := (Lg E [eta cpow x]).
have cf: cardinal_fam f by rewrite/f;hnf;aw => t te; rewrite LgV//; fprops.
set s:= (union (range f)).
have <-: s = union (fun_image E (cpow x)) by rewrite /s Lg_range.
have cy:=(proj1 icy).
move: (infinite_power7d cy (infinite_nz icy)); rewrite -/E; move => [pw _].
suff aux: y <=c s.
  symmetry; apply: csum_of_small_b4; fprops.
  - apply: (cle_inf_inf icy aux). 
  - by  move: (cleT pw aux); aw. 
have fgf: fgraph f by rewrite /f; fprops.
have csr: cardinal_set (range f).
  move => t /(range_gP fgf); rewrite /f;aw;move => [z ze ->]; rewrite LgV//; fprops.
case: (cleT_el cy (CS_sup csr)) => //; rewrite -/s => sy.
move: (cantor (CS_sup csr)); rewrite -/s => /cltNge; case.
have sE: inc s E by apply /(cardinals_ltP cy).
apply: (cleT (cpow_Mleeq s xy card2_nz)).
apply: card_sup_ub => //; apply /(range_gP fgf). 
by rewrite /f; aw;ex_tac; rewrite LgV.
Qed.

Lemma cpow_less_pr1 x y:  \0c <c x -> cardinalp y -> x ^<c y <=c x ^c y.
Proof. 
move=> [[_ cx _] xnz] cy; apply:card_ub_sup; fprops.
move => t /funI_P [z zy ->]; apply: cpow_Mlele => //.
- by apply:nesym.
- by apply:cleR.
- by move: zy => /cardinals_ltP [].
Qed.

Lemma cpow_less_pr2 x y z: z <c y -> x ^c z <=c (x ^<c y).
Proof. 
move=> lt1; apply: card_sup_ub; first by apply: cpow_less_pr0. 
apply /funI_P;exists z => //; apply /(cardinals_ltP (proj32_1 lt1)) => //.
Qed.


Lemma cpow_less_pr3 x y: \0c <c x -> natp y ->
  x ^<c (csucc y) = x ^c y.
Proof.  
move=> [[_ cx _] xnz] yN.
apply: cleA; last by apply: cpow_less_pr2; apply: cltS.
apply: card_ub_sup.
- fprops.
- move => i /funI_P [z zi ->]; apply: cpow_Mlele; fprops.
  have cs: cardinalp (csucc y) by apply: CS_succ.
  by move: zi => /(cardinals_ltP cs) /(cltSleP yN).
Qed.

Lemma cpow_less_pr4 x y: \0c <c x -> infinite_c y ->
  x ^<c (cnext y) = x ^c y.
Proof.  
move=> [[_ cx _] xnz] yi.
have cy := proj1 yi.
apply: cleA; last by (apply: cpow_less_pr2; apply:(cnext_pr2 cy)).
apply: card_ub_sup.
- fprops.
- move => i /funI_P [z /Zo_hi zi ->]; apply: cpow_Meqle;fprops.
  apply: cnext_pr4 => //. 
Qed.

Lemma CS_cpow_less x y: cardinalp (x ^<c y).
Proof. apply: CS_sup; apply: cpow_less_pr0. Qed.

Lemma cpow_less_compare x: infinite_c x ->
  (x <=c \2c ^<c x /\ \2c ^<c x <=c x ^<c x /\ x ^<c x <=c x ^c x).
Proof.
move => icx; move: (proj1 icx) => cx.
have x2:= (infinite_ge2 icx).
split.
  move: (@cpow_less_pr0 \2c x) => aux.
  case: (cleT_el cx (CS_cpow_less \2c x)) => // pa.
  set u := \2c ^<c x.
  have le : \2c ^c u <=c u. 
     apply: card_sup_ub => //; apply /funI_P;exists u => //.
     apply /cardinals_ltP => //.
  case: (cleNgt le (cantor (proj31_1 pa))).
split.
  apply: card_sup_image; move=> t tx; apply: (cpow_Mleeq _ x2);fprops.
apply: cpow_less_pr1 => //; split; first by apply: cle0x. 
exact: (nesym (infinite_nz icx)).
Qed.


Lemma cpow_less_pr5a x y: cardinalp x -> \2c <=c y -> x <=c x ^<c y.
Proof.
move=> cx y2. 
move: (cpow_less_pr2 x (clt_leT (clt_12) y2)).
by rewrite cpowx1.
Qed.

Lemma cpow_less_pr5b x y: infinite_c x -> \2c <=c y -> infinite_c (x ^<c y).
Proof.
move=> cx y2; apply: (cle_inf_inf cx (cpow_less_pr5a (proj1 cx) y2)).
Qed.

Lemma cpow_less_pr5c x: \2c <=c x -> finite_c x ->  x ^<c  omega0 = omega0.
Proof.
move => x2 xf.
have co:= CS_omega.
have aux:= (@cpow_less_pr0 x omega0).
have oic:= CIS_omega.
have xb: natp x by apply /NatP.
have le1: x ^<c omega0 <=c omega0.
  apply:card_ub_sup => // i /funI_P [z zx ->].
  move: zx => /(cardinals_ltP co) zx.
  by apply: cle_fin_inf => //;apply /NatP; apply (NS_pow xb); apply/clt_omegaP.
ex_middle neq1.
set t :=  x ^<c omega0.
have to: t <c omega0 by split.
have pb:= (cantor (proj31_1 to)).
case: (cleNgt  (cpow_less_pr2 x to) (clt_leT pb (cpow_Mleeq t x2 card2_nz))).
Qed.

Lemma cpow_less_pr5d : \2c ^<c  omega0 = omega0.
Proof.
apply: cpow_less_pr5c finite_2; apply: (cleR CS2).
Qed.

Lemma cpow_less_pr5e x:  infinite_c x -> x ^<c omega0 = x.
Proof.
move => icx; move: (proj1 icx) => cx.
apply: cleA (cpow_less_pr5a cx (infinite_ge2 CIS_omega)).
apply: card_ub_sup => // i /funI_P [z za ->]; move: za.
move /(cardinals_ltP CS_omega) => za.
move: (oclt za) => /oltP0; move=> [_ _ xn].
by apply: cpow_inf1.
Qed.

Lemma cpow_less_pr5f (x := omega0):  x ^<c x = x.
Proof. by apply: cpow_less_pr5e; apply: CIS_omega. Qed.

Lemma cpow_less_pr6 x z: infinite_c x -> \2c <=c z ->
  z ^c x = (z ^<c x ) ^c (\cf x).
Proof.
move => icx t2.
move: (cofinality_c_pr3 icx) => [f [ [[pa1 pa2 pb pc] pd] _]].
apply: cleA.
  rewrite - (cofinality_card icx) -{1} pd (cpow_sum _ f). 
  rewrite - pc - cprod_of_same /cst_graph; aw.
  apply: cprod_increasing; aww => t td; rewrite !LgV//.
  by apply: cpow_less_pr2; apply: pb.
have tp:=(clt_leT clt_02 t2).
have h:= (cpow_less_pr1 tp (proj1 icx)).
have cnz:= (infinite_nz (cofinality_infinite_cardinal icx)).
case: (equal_or_not (z ^<c x) \0c) => aux.
  by rewrite aux (cpow0x cnz); apply: (cle0x (proj32 h)).
move: (cpow_Mleeq (\cf x) h aux).
by rewrite - cpow_pow (cprod_inf  (cofinality_small icx) icx cnz).
Qed.

Lemma cpow_less_pr6a x: infinite_c x ->
  \2c ^c x = (\2c ^<c x ) ^c (\cf x).
Proof.
move => icx; apply: cpow_less_pr6 => //; fprops.
Qed.

Lemma cpow_less_pr7a x: infinite_c x ->
  csumb (cardinals_le x) (fun t => x ^c t) = \2c ^c x.
Proof.
move => icx; move: (icx) => [cx _].
set f := (Lg (cardinals_le x) [eta cpow x]).
set a := cardinals_lt x.
have h1P:= (cardinals_ltP cx).
have h2P:= (cardinals_leP cx).
have fgf: fgraph f by rewrite /f; fprops.
have pa:  (a +s1 x) =  (domain f). 
  rewrite /f /a; aw; set_extens t.
    case/setU1_P => ha;apply /h2P; [by move/h1P: ha => []| rewrite ha; fprops].
  move /h2P=> aux; apply /setU1_P; case:(equal_or_not t x) => tx; [by right |].
   by left ; apply /h1P; split.
have pb: sub (a +s1 x) (domain f) by rewrite pa; fprops.
have pc: ~(inc x a) by move /h1P => [_].
move: (induction_sum0 f pc).
rewrite pa (restr_to_domain fgf  (@sub_refl f)) /csumb; move => ->.
have pd : inc x (cardinals_le x) by apply/ h2P; fprops.
have ->: (restr f a) = Lg a (cpow x).
  apply: Lg_exten => t tx; rewrite /f LgV//.
    move: pa; rewrite /f Lgd;move => <-; fprops.
rewrite -/(csumb _ _) - (cpow_less_alt icx (infinite_ge2 icx)).
move: (cpow_less_compare icx) => [_ [_ pe]].
rewrite /f LgV//-(infinite_power1_b icx).
rewrite csumC (csum_inf pe) //; apply: CIS_pow => //.
by apply: infinite_nz.
Qed.

Lemma cpow_less_pr7b x (y := cnext x) : infinite_c x ->
  csumb (cardinals_lt y) (fun t => y ^c t) = \2c ^c x.
Proof.
move => icx; move: (icx) => [cx _].
have pa:=(cnext_pr2 cx).
have iy:= (cle_inf_inf icx (proj1 pa)).
have y2:= (infinite_ge2 iy).
have qa:= (clt_leT clt_02 y2).
rewrite - (cpow_less_alt iy y2).
by rewrite (cpow_less_pr4 qa icx) infinite_power1 //; apply: cnext_pr3.
Qed.

Lemma cpow_less_pr8 x:
   infinite_c x -> (forall y, y<c x -> \2c ^c y <c x) ->
   [/\ \2c ^c x = gimel_fct x,
     x <c (\cf (gimel_fct x)) &
     (\cf x = omega0 ->  \2c ^c x = x ^c omega0)].
Proof.
move => icx h.
 have cx := proj1 icx.
have pa:  \2c ^c x = gimel_fct x.
  rewrite (cpow_less_pr6a icx).
  have le1 : (\2c ^<c x) <=c x.
    apply: card_ub_sup; first exact: cx.
    move =>i /funI_P [z] /(cardinals_ltP cx) pa.
    move => ->; apply: (proj1 (h _ pa)).
  by rewrite (cleA le1 (proj1 (cpow_less_compare icx))).
split; first by exact.
   by rewrite -pa; apply: power_cofinality2.
by rewrite pa /gimel_fct => ->.
Qed.

Lemma cpow_less_pr9 x (y := cnext x):
  infinite_c x -> ( y ^<c y = \2c ^c x /\ \2c ^<c y = \2c ^c x).
Proof.
move => icx; move: (icx) => [cx _].
have sp:= (cle_ltT(cle0x cx) (cnext_pr2 cx)).
rewrite (cpow_less_pr4 clt_02 icx) (cpow_less_pr4 sp icx).
by rewrite (infinite_power1_c icx). 
Qed.


Definition cpow_less_ecb x := 
 (exists2 a, a <c x & forall b, a <=c b -> b <c x -> \2c ^c a = \2c ^c b).

Lemma cpow_less_pr10 x: singular_cardinal x -> (cpow_less_ecb x)
  -> \2c ^c x = \2c ^<c x. 
Proof.
move => [icx sx] [a ax ha].
have H:=(cofinality_card icx).
have cg:= (cofinality_small icx).
have [c [ac cf cx]]: exists c, [/\ a <=c c, \cf x <=c c& c <c x].
  have ca:= proj31_1 ax.
  have cx:=(proj31 cg); have le1:= (cleR cx); have le2:= (cleR ca).
  case: (cleT_ee ca cx) => h; first by exists  (\cf x). 
  by exists a.
have p2: (\2c ^<c x) = \2c ^c c.
  apply: cleA (cpow_less_pr2 \2c cx).
  apply: card_ub_sup ;first fprops.
  move=> i /funI_P [z zi ->].
  move: zi => /(cardinals_ltP (proj1 icx)) zx.
  case: (cleT_ee (proj31_1 zx) (proj31_1 cx)) => zc.
    apply: cpow_Mlele ; fprops.
  rewrite - (ha _ (cleT ac zc) zx); apply: cpow_Mlele ; fprops.
move: (cpow_less_pr6a icx).
move: (cofinality_infinite icx); rewrite H => coi.
have cnz := (infinite_nz coi).
rewrite p2 - cpow_pow cprod_inf//; apply (cle_inf_inf coi cf).
Qed.

Lemma gimel_prop n (x:= \aleph n): ordinalp n ->
 [/\  (n = \0c  -> \2c ^c x = gimel_fct x),
    (osuccp n) -> \2c ^c x = gimel_fct x,
    (limit_ordinal n -> cpow_less_ecb x -> 
       \2c ^c x = \2c ^<c x *c  gimel_fct x)&
    (limit_ordinal n -> not (cpow_less_ecb x) -> 
       \2c ^c x = gimel_fct (\2c ^<c x))].
Proof.
move => on.
have res1:  n = \0c -> \2c ^c x = gimel_fct x.
   move => h; symmetry; apply: gimel_prop1.
   by rewrite /x h aleph0E; apply: regular_cardinal_omega.
have res2: osuccp n -> \2c ^c x = gimel_fct x.
  move => [m om nm]; symmetry.
  move: (regular_initial_successor om); rewrite -nm;apply: gimel_prop1.
move: (CIS_aleph on); rewrite -/x => icx.
move: (cofinality_infinite_cardinal icx)(gimel_prop2 icx)(icx) => coi g2 [cx _].
have pa: limit_ordinal n -> infinite_c (\2c ^<c x).
  move => ln.
  have h:= (cpow_less_pr2 \2c (aleph_lt_ltc (limit_pos ln))).
  have ip2o:= (infinite_pow2 (CIS_aleph OS0)).
  exact (cle_inf_inf ip2o h).
split => //.
  move=> ln cs; move: (infinite_pow2 icx) => ip2x.
  case: (equal_or_not x (\cf x)) => xcx.
     have rx: regular_cardinal x by apply /regular_cardinalP.
     rewrite (gimel_prop1 rx) cprodC; symmetry; apply cprod_inf => //.
       apply: (cpow_less_pr1 clt_02 cx).
     exact (infinite_nz (pa ln)).
  have si: singular_cardinal x by split => //; apply:nesym.
  rewrite - (cpow_less_pr10 si cs).
  symmetry; apply cprod_inf => //.
  apply: infinite_nz; apply: CIS_pow2 => //.
move => ln nl.
have paln:= (pa ln).
rewrite /gimel_fct (cpow_less_pr6a icx).
suff aux: \cf (\2c ^<c x) = \cf  x by ue.
have ox: ordinalp x by apply: OS_cardinal.
have oy: ordinalp  (\2c ^<c x) by move: paln => [pb _]; apply: OS_cardinal.
move: (cofinality_rw ox) (cofinality_rw oy) => [qa qb qc] [qd qe qf].
have x1: forall t, t <c x -> \2c ^c t <c \2c ^<c x. 
  move => t tx; split; first by apply:  cpow_less_pr2.
  move => ub; case: nl; exists t => //.
  move => b b1 b2.
  move: (cpow_M2le b1) (cpow_less_pr2 \2c b2); rewrite - ub.
  apply:cleA.
have x2: forall t,  t <o \2c ^<c x -> exists2 u, t <=o \2c ^c u & u <c x.
  move => t tl.
  have ot:= proj31_1 tl.
  move /(ocle2P (proj1 paln) ot): tl => tl.
  case: (oleT_el OS_omega ot) => cto; last first.
    exists omega0.
      exact (oleT (proj1 cto) (proj1 (oclt (cantor CS_omega)))).
    rewrite - aleph0E; apply: aleph_lt_ltc.
    by move: ln => [_ ok _]; apply /oltP.
  move: (infinite_set_pr3 cto) => /infinite_setP ict.
  move: (cnext_pr1 (proj1 ict)) => []; set st := cnext (cardinal t).
  move=> sa sc sb; move: (sb _ tl) => sd.
  set sst:= Yo (cardinalp t) t st.
  have pc: t <=o sst.
     rewrite /sst; Ytac ct; first by apply: oleR.
     case: (oleT_ee ot (proj1 sa)) => // xx.
     by move: (ocle1 xx); rewrite -/st (card_card sa) =>/(cltNge sc).
  have sdd : sst <c \2c ^<c x.
    rewrite /sst; Ytac ct; first by rewrite - (card_card ct).
    split; [by apply: sd | move => bad ].
    case: (p_or_not_p (exists2 u, u <c x & \2c ^c u = \2c ^<c x)) => H.
      by move: H => [u ua ub]; move: (x1 _ ua) => [_ xbad].
    have bad2: forall w, w <c x -> \2c ^c w <=c (cardinal t).
      move=> w wc;apply: (cnext_pr4 (proj1 ict));  rewrite -/st bad; split.
        exact: (cpow_less_pr2 \2c wc). 
      by move => eq; case: H; exists w.
    have bad3: \2c ^<c x <=c cardinal t.
      apply: card_ub_sup; first apply: CS_cardinal.
      by move=> i /funI_P [z zs ->]; apply: bad2; apply /(cardinals_ltP cx).
    case: (cltNge sc (cleT sd bad3)).
  suff: (exists2 u, sst <=c \2c ^c u & u <c x).
    move => [u /ocle p1 p2]; exists u => //; exact: (oleT pc p1).
  ex_middle bad; case: (cltNge sdd).
  have cs:= (proj31_1 sdd).
  apply:card_ub_sup; first exact cs.
  move =>i /funI_P [z /(cardinals_ltP cx) zx ->].
  have c2: cardinalp (\2c ^c z) by fprops.
  by case: (cleT_ee cs c2) => // le4; case: bad; exists z.
apply: oleA.
  move: (qb) => [f [[ff sf tf] cf]].
  set g := Lf (fun z => \2c ^c (Vf f z)) (\cf x) (\2c ^<c x).
  have ta: lf_axiom (fun z => \2c ^c (Vf f z)) (\cf x) (\2c ^<c x).
    rewrite - sf; move => t ts /=; rewrite - cpowcr.
    set zz := cardinal _.
    have zzx: zz <c x by apply:colt1=> //;rewrite -tf; fprops.
    move: (cpow_less_pr2 \2c zzx) => [a1 a2 a3].
    case: (ordinal_sub (OS_cardinal a1) (OS_cardinal a2) a3) => // eq1.
    by move: (proj2 (x1 _ zzx)); rewrite eq1. 
  have fg: function g by apply: lf_function.
  apply: (qf _ qa); exists g.
  split; [ by hnf; rewrite /g; split => //; aw | move  => t tp].
  have tl: t <o (\2c ^<c x) by apply/oltP.
  move: (x2 _ tl) => [u u1 u2]. 
  have ui: inc u x by move: (oclt u2) => /oltP0 [_ _].
  move: (cf _ ui) => [z zx le2]; exists z => //.
  rewrite /g LfV//.
  have le3:= (ocle1 le2).
  move: (cpow_M2le le3); rewrite cpowcr cpowcr.
  move => le4; exact: (oleT u1 (ocle le4)).
move: (qe) => [f [[ff sf tf] cf]].
pose g t := choose (fun u => (Vf f t <o \2c ^c u /\ u <c x)).
have gp: forall t, inc t (source f)-> (Vf f t <o \2c ^c (g t) /\ (g t) <c x).
   move => t /(Vf_target ff); rewrite tf => xx.
   have [sa _ sc]:= (infinite_card_limit2 paln).
   move/(oltP sa): (sc _ xx) => /x2 [u /oleSltP aux ux].
   by apply choose_pr; exists u.
set G:= Lf g (cofinality (\2c ^<c x)) x.
have ta: lf_axiom g (cofinality (\2c ^<c x)) x.
  move => t;  rewrite - sf => stf; move: (gp _ stf) => [_]. 
  by move /oclt =>/(oltP0) [_ _].
apply: qc => //; exists G; split.
  by rewrite /G; hnf; aw;split => //; apply: lf_function.
move=> t tx; ex_middle bad.
have pb: forall z, inc z (cofinality (\2c ^<c x)) -> Vf G z <o t.
  move => z zsf; move: (zsf); rewrite - sf => zt.
  have ow: ordinalp (Vf G z). 
    rewrite /G !LfV//;exact: (OS_cardinal (proj31_1 (proj2 (gp _ zt)))).
  case: (oleT_el (Os_ordinal ox tx) ow) => // yy; case: bad; ex_tac.
have pc: forall z, inc z (cofinality (\2c ^<c x)) -> Vf f z <o \2c ^c t.
  move => z zc;move: (zc); rewrite - sf => /gp [lt1 _].
  move: (pb _ zc); rewrite /G LfV//; move => [] /ocle1 /cpow_M2le.
  rewrite cpowcr cpowcr => /ocle x6 _; apply:(olt_leT lt1 x6).
have bad2:  inc (\2c ^c t) (\2c ^<c x).
  have:  (\2c ^c t) <c (\2c ^<c x).
    rewrite - cpowcr.
    have ot:= (Os_ordinal ox tx).
    by apply: x1 ; apply /(ocle2P cx ot); apply /oltP.
  by move => x3; move: (oclt  x3); move/(oltP oy).
by move: (cf _ bad2) => [z zc le]; move: (oleNgt le (pc _ zc)).
Qed.


Lemma gimel_prop3 x: infinite_c x ->
  [/\ (regular_cardinal x -> \2c ^c x = gimel_fct x),
      (singular_cardinal x -> cpow_less_ecb x ->  \2c ^c x = \2c ^<c x) &
     (singular_cardinal x -> not (cpow_less_ecb x) ->  
     \2c ^c x = gimel_fct (\2c ^<c x))].
Proof.
move => icx.
move: (ord_index_pr1 icx); set n :=  (ord_index x); move => [pa pb].
have qa: singular_cardinal x -> limit_ordinal n.
  by rewrite - pb; apply: singular_limit.
move: (gimel_prop pa) => [pc pd pe pf].
rewrite pb in pe pf.
split; first by symmetry;apply: gimel_prop1.
   by move  => qb qc;  rewrite cpow_less_pr10. 
by move => qb qc; exact (pf (qa qb) qc).
Qed.


Definition cpow_less_ec_prop x y a:=
  a <c y /\ forall b,  a<=c b -> b <c y ->  x ^c a = x ^c b.


Lemma cpow_less_ec_pr0 x y:
  infinite_c y -> \2c <=c x -> infinite_c  (x ^<c y).
Proof.
move => icy x2.
have pa: forall n, natp n -> n <=c x ^<c y.
  move => n nN; apply (cleT (proj1 (cantor (CS_nat nN)))).
  move: nN => /NatP nN.
  apply: cleT _ (cpow_less_pr2 x (clt_fin_inf nN icy)).
  by apply: cpow_Mleeq => //; apply: card2_nz.
apply: (cle_inf_inf CIS_omega).
by rewrite omega_limit0; apply: (card_ub_sup (proj32 (pa _ NS2))).
Qed.

Lemma cpow_less_ec_pr1 x y:
  cardinalp  y ->  exists a, cpow_less_ec_prop x (cnext y) a.
Proof.
move=> cy.
exists y; split; first by move: (cnext_pr1 cy) => [_ pb _].
move => b yb /(cnext_pr4 cy) bs; by rewrite (cleA  bs yb).
Qed.

Lemma card_ge2_nz  x: \2c <=c  x -> x <> \0c.
Proof.
move => x2.
exact: (nesym (proj2 (clt_leT clt_02 x2))).
Qed.

Lemma cpow_less_ec_pr2 x y a:
  cpow_less_ec_prop x y a -> \2c <=c x ->
  forall b,  a<=c b -> b <c y  ->  x ^<c y = x ^c b.
Proof.  
move =>[ay h] x2 b le1 le2.
have xnz := (card_ge2_nz x2).
apply: cleA; last by apply: cpow_less_pr2.
have cy:= proj32_1 le2.
apply: card_ub_sup; first fprops.
move => i /funI_P [z /(cardinals_ltP cy) lt1 ->].
case: (cleT_ee (proj31 le1) (proj31_1 lt1)) => az.
  rewrite - (h _ az lt1) (h _ le1 le2).
  apply: (cleR); fprops.
exact (cpow_Meqle xnz (cleT az le1)).
Qed.

Lemma cpow_less_ec_pr3 x y a:
  cpow_less_ec_prop x y a -> \2c <=c x -> singular_cardinal y ->
   (x ^<c y = x ^c a /\ x ^<c y = x ^c y).
Proof.
move => h x2 [icy sy]; move: (h) => [ay h0].
have h1:= (cpow_less_ec_pr2 h x2).
have ca:= (proj31_1 ay).
rewrite (h1 _ (cleR ca) ay).
split; first by exact.
have cg:= (cofinality_small icy).
have [c [ac cf cx]]: exists c, [/\  a <=c c, \cf y <=c c &c <c y].
  have cx:= proj31 cg.
  case: (cleT_ee ca cx) => cp; last by exists a; split;fprops.
  exists  (\cf y); split => //; split; fprops.
have coi:=(cofinality_infinite_cardinal icy).
have cnz:=(infinite_nz coi).
have icc:= (cle_inf_inf coi cf).
rewrite (cpow_less_pr6 icy x2) (h1 _ ac cx) - cpow_pow.
by rewrite  (cprod_inf cf icc cnz) (h0 _ ac cx).
Qed.

Lemma cpow_less_ec_pr4 x y:
  infinite_c y -> \2c <=c x ->
  (exists a, cpow_less_ec_prop x y a) ->
  y <=c \cf (x ^<c y).
Proof.
move => icy x2 [a ha].
have hb:= (cpow_less_ec_pr2 ha x2).
move: (ord_index_pr1 icy); set i := ord_index y; move=> [oi yv].
have xnz: \0c <c x by apply: clt_leT clt_02 x2.
case: (ordinal_limA oi) => li.
    have yo: y = omega0 by  rewrite -yv li aleph0E.
    move: ha => [ay h1].
    rewrite (hb _ (cleR (proj31_1 ay)) ay).
    move: (oclt ay); rewrite yo => /olt_omegaP aN.
    have sN:= (NS_succ aN). 
    have sy: (csucc a) <c y.
      rewrite yo; apply: clt_fin_inf => //; first by apply /NatP.
      apply: CIS_omega.
    have eq1:= (h1 _ (cleS aN) sy).
    case: (finite_or_infinite (proj32 x2)) => icx.
      have xN: natp x by apply /NatP.
      have x1:=(clt_leT (clt_12) x2).
      by move: (cpow_Meqlt xN sN (cltS aN) x1) => [_ bad]; case: bad.
    have pa:= (cofinality_infinite_cardinal (CIS_pow icx (@succ_nz a))).
    by rewrite eq1;apply /infinite_c_P2.
  move: li => [j oj jv].
  have ->: y = cnext (\aleph j) by rewrite -yv jv cnextE.
  have ipy:= (CIS_aleph oj).
  rewrite (cpow_less_pr4 xnz ipy).
  by move: (power_cofinality5 x2 ipy)(cnext_pr1 (proj1 ipy)) => s [_ _]; apply.
rewrite -yv.
rewrite {1} (proj2 (aleph_normal) _ li). 
move: (ha) => [ay _]; move: (ay) => [[ca _] _ _].
have aa:= cleR ca.
have [c [ic ac cy]]: exists c, [/\  infinite_c c, a <=c c & c <c y].
  case: (finite_or_infinite ca); last by exists a. 
  have io:= CIS_omega.
  move => fa; exists omega0; split => //; first by apply: cle_fin_inf.
  rewrite - aleph0E -yv; apply: aleph_lt_ltc.
  by move: li => [ori zi _]; apply/oltP.
rewrite yv (hb _ ac cy).
apply: card_ub_sup.
   apply: CS_cofinality; exact: (proj1 (CS_pow x c)).
move => t /funI_P [z zi ->].
have zi1: z <o i by move: zi => /oltP [].
move: (aleph_lt_ltc zi1); rewrite yv => lt.
move: (ic) => [cc _].
case: (cleT_el cc (proj31_1 lt)) => le1.
  rewrite - (hb _ ac cy) (hb _ (cleT ac le1) lt).
  apply: (proj1 (power_cofinality5 x2  (CIS_aleph (proj31_1 zi1)))).
exact:(cleT (proj1 le1) (proj1 (power_cofinality5 x2 ic))).
Qed.

Lemma cpow_less_ec_pr5 x y:
  infinite_c y -> \2c <=c x ->
  ~ (exists a, cpow_less_ec_prop x y a) ->
  exists X, let Y := Lg (domain X) (fun z => x ^c (Vg X z)) in
    [/\ domain X = \cf y,
     (forall i, inc i (domain X) -> Vg X i <c y),
     (forall i, inc i (domain X) -> Vg Y i <c  x ^<c y),
     (y <> omega0 -> card_nz_fam X) &
     \csup (range Y) = x ^<c y ].
Proof.
move => icy x2 ha.
move: (ord_index_pr1 icy); set c := ord_index y; move => [oc yv].
case: (equal_or_not c \0c)=> cz.
  have yo: y = omega0 by rewrite -yv cz aleph0E.
  have oic:=CIS_omega.
  case: (finite_or_infinite (proj32 x2)) => fcx; last first.
    case: ha; rewrite yo;exists \1c; split; first by apply /clt_omegaP; fprops.
    move => b b1 bo.
    have bnz: b <> \0c by  move/cge1P:b1 => [_ /nesym].
    by rewrite(cpowx1 (proj1 fcx)) (cpow_inf fcx) //;apply /clt_omegaP.
  exists (Lg y id); simpl; rewrite yo; split => //.
  - by aw; rewrite (proj2 (regular_omega)).  
  - by hnf;aw;move => a ay; rewrite LgV//; apply/clt_omegaP.
  - aw => i ib; rewrite !LgV//; rewrite (cpow_less_pr5c x2 fcx). 
    by apply/clt_omegaP; fprops.
  - aw; rewrite /cpow_less Lg_range; congr union.
    set_extens t;move /funI_P => [z zo ->]; apply/funI_P.
      exists z; first by apply/(cardinals_ltP CS_omega); apply/clt_omegaP.
      by rewrite LgV.
    move /(cardinals_ltP CS_omega): zo => /clt_omegaP zb; exists z => //.
   by erewrite LgV.
case: (ordinal_limA oc) => // lc.
  move: lc => [d od dv]; case: ha; exists (\aleph d).
  have ipy := (CIS_aleph od).
  move: (cnext_pr1 (proj1 ipy)) => [pb pc pd].
  move: (cnextE od); rewrite -dv yv => <-; split => //. 
  by move => b l1 /(cnext_pr4 (proj1 ipy)) pe; rewrite (cleA l1 pe).
have xnz:= (card_ge2_nz x2).
have pa: forall a, a <c y -> exists b, [/\ a <c b, b <c y & x ^c a <c x^c b].
  move => a ay; ex_middle bad; case: ha; exists a; split => //.
  move => b ab lby; ex_middle ne.
  case: bad; exists b; split => //; split => //; first by dneg eq0; rewrite eq0.
  exact: (cpow_Meqle xnz ab).
have cfy:= (regular_initial_limit1 lc).
move: (cofinality_pr4 (proj31 lc)); rewrite - cfy yv; move=> [f fa qe].
move: fa; set cy := \cf y; move => [[[ff sf tf]] cff [_ nf nf1]].
set X := Lg cy (fun z => \aleph (Vf f z)).
have fap: forall z, inc z cy -> inc (Vf f z) c. 
  by move => z zx; rewrite -tf; Wtac.
have faq: forall z, inc z cy -> ordinalp (Vf f z). 
   move=> z zx; exact: (Os_ordinal oc (fap _ zx)).
have pb: cardinal_fam X.
  by rewrite /X;hnf;aw; move => a ay; rewrite LgV//;apply: CS_aleph; apply: faq.
have pc: fg_Mlt_ltc X.
  hnf; rewrite /X Lgd;move => a b ac bc ab; rewrite !LgV//;apply: aleph_lt_ltc.
  by apply: nf.
have pb':  fgraph X  by rewrite /X; fprops.
have pd: cardinal_set (range X).
  by move => t /(range_gP pb') [z zd ->]; apply: pb.
have pe: \osup (range X) = y.
  set S := \osup (range X); move: (proj1 icy) => ccy.
  case: (cleT_el ccy (CS_sup pd)) => pr1.
    apply:cleA => //; apply: card_ub_sup=> // i /(range_gP pb'). 
    rewrite /X; aw; move => [z zy ->]; rewrite LgV//; move /(oltP oc): (fap _ zy) => [].
    by rewrite - yv => /aleph_le_lec.
  have [ra rb rc]: limit_ordinal cy.
    apply: infinite_card_limit2.
    by rewrite /cy  - yv cfy; apply: cofinality_infinite_limit.
  have: infinite_c S. 
     have: inc (\aleph (Vf f \0c)) (range X).
       by apply /(range_gP pb'); rewrite /X; aw; ex_tac; rewrite LgV.
     move /(card_sup_ub pd); apply: cle_inf_inf; apply: CIS_aleph.
     by apply: faq.
  move/ord_index_pr1 => []; set s := ord_index S => os sv.
  move: pr1; rewrite - /S - sv - yv; move /(aleph_ltc_lt os oc). 
  move: lc => [_ c0 cl]; move => /(oltP oc) /cl /cff [z zc h].
  have: inc (\aleph (Vf f z)) (range X). 
     by apply /(range_gP pb'); rewrite /X; aw; ex_tac; rewrite LgV.
  move/(card_sup_ub pd); rewrite -/S - sv; move /(aleph_lec_le(proj32 h) os). 
  by move /oltSleP => /(oleNgt h).
have pi : card_nz_fam X.
  by rewrite /X; hnf; aw; move => i idx; rewrite LgV//; apply: aleph_nz; apply: faq.
have ph: (forall i, inc i (domain X) -> Vg X i <c y).
  rewrite /X; aw; move => i ic;rewrite LgV//; rewrite -yv.
  apply: aleph_lt_ltc; move: (fap _ ic).
  by move /(oltP oc).
set Y := (Lg (domain X) (fun z => x ^c (Vg X z))).
have pf: forall i, inc i (domain X) -> Vg Y i <c x ^<c y.
  move => i idx; rewrite /Y LgV//.
  move: (ph _ idx) => /pa [b [ba /(cpow_less_pr2 x) bb bc]]. 
  exact:(clt_leT bc bb).
have pg: union (range Y) = x ^<c y.
  have rb: fgraph Y by rewrite /Y;fprops.
  have ra:cardinal_set (range Y).
    move => t/ (range_gP rb); rewrite /Y; aw; move => [u ud ->]; rewrite LgV//; fprops.
  have rc: cardinalp (x ^<c y) by apply: CS_cpow_less.
  have rd: cardinalp (union (range Y)) by apply: CS_sup.
  move: (@cpow_less_pr0 x y) => re.
  apply: cleA.
    apply: card_ub_sup => // i /(range_gP rb). 
    by move=> [z]; rewrite {1}/ Y; aw => /pf [] h _ ->.
  apply: card_ub_sup => // i /funI_P [z].
  move /(cardinals_ltP (proj1 icy)) => rf ->.
  have [t tr xt]: exists2 t, inc t (range X) & z <=c t.
     ex_middle bad; case:(cltNge rf). 
     have ccz := proj31_1 rf.
     rewrite -pe; apply : card_ub_sup => //.
     move => j jr; case: (cleT_ee (pd _ jr) (proj31_1 rf)) => //.
     move => zj; case: bad; ex_tac.
  apply: (cleT (cpow_Meqle xnz xt)).
  have fgx:fgraph X by rewrite /X; fprops.
  move: tr => /(range_gP fgx) [v va ->].
  apply: card_sup_ub => //; apply /(range_gP rb); aw.
  by rewrite /Y; aw; ex_tac; rewrite LgV.
by exists X; split => //; rewrite /X; aw.
Qed.


(* wwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwwww *)



Lemma cpow_less_ec_pr6 x y:
  infinite_c y -> \2c <=c x ->
  ~ (exists a, cpow_less_ec_prop x y a) ->
  \cf (x ^<c y) = \cf y.
Proof.
move => pa pb pc.
symmetry.
move: (cpow_less_ec_pr5 pa pb pc) => [X [q1 q2 q3 q4 q5]].
have icz: infinite_c (x ^<c y) by apply: cpow_less_ec_pr0.
have fgY: fgraph (Lg (domain X) (fun z : Set => x ^c Vg X z))  by fprops.
move: (icz) => [[oz _] _]; move: (icz) => [cz _].
apply: cleA; last first.
  move: q5; set v := range _ => e1.
  have h: sub v (x ^<c y).
     move => t /(range_gP fgY);aw; move => [z /q3 h ->].
     by move :(oclt h) => /(oltP oz).
  move: (cofinality_pr8 oz h e1).  
  move: (range_smaller fgY); rewrite -/v q1 Lgd.
  rewrite (card_card (CS_cofinality (proj1 (proj1 pa)))) => l1 l2.
  exact: cleT l2 l1.
move: (cofinality_pr4 oz).
move => [f [[[ff sf tf] cff] fb] fc].
have xnz:= (card_ge2_nz pb). 
have ra: forall a, a <c y -> exists b, [/\ a <c b, b <c y & x ^c a <c x^c b].
  move => a ay; ex_middle bad; case: pc; exists a; split => //.
  move => b ab lby; ex_middle ne.
  case: bad; exists b; split => //; split => //; first by dneg eq0; rewrite eq0.
  exact  (cpow_Meqle xnz ab).
have rb: forall i, inc i (source f) -> 
   exists t, inc t y /\ cardinal (Vf f i) <=c x ^c t.
  move => i isf.
  have /(oltP oz) la: inc  (Vf f i) (x ^<c y) by rewrite - tf; Wtac.
  have ou:= proj31_1 la.
  move/(ocle2P cz ou): la => lb.
  move:pa => [cy _]; move: (cy) => [oy _].
  move: (clt_sup (@cpow_less_pr0 x y) lb) => [v /funI_P[w]].
  move /(cardinals_ltP cy)=> /oclt => rb -> /proj1 rc.
  by exists w; split => //; apply /(oltP oy).
pose g i := choose (fun t => inc t y /\ cardinal (Vf f i) <=c x ^c t).
have gp: forall i, inc i (source f) ->
     inc (g i) y /\ cardinal (Vf f i) <=c x ^c (g i).
  move => i /rb h; apply: (choose_pr h).
move: (fun_image_smaller (source f) g).
have oy:=(proj1 (proj1 pa)).
set G := fun_image (source f) g; rewrite sf (card_card (CS_cofinality oz)).
have sgy: sub G y by move => t /funI_P [z /gp [  h _] ->].
suff ugy: \osup G = y by apply: cleT; exact (cofinality_pr8 oy sgy ugy).
have osy: ordinal_set y by  move => t/(Os_ordinal oy).
have ->: y = union y.
 by move: (limit_nonsucc (infinite_card_limit2 pa)).
apply: (ord_sup_1cofinal) => //; split => // a /(oltP oy) lay.
have oa:= proj31_1 lay.
move /(ocle2P (proj1 pa) oa): lay => /ra [b [sa sb sc]].
have: inc (x ^c b) (x ^<c y).
   apply /(oltP oz); move: (ra _ sb) => [b' [b1 b2 b3]].
   move: (clt_leT b3 (cpow_less_pr2 x b2)).
   apply: oclt.
rewrite - sf in cff; move /cff => [c c1 /ocle1 c2].
exists (g c); first by apply/funI_P; ex_tac.
move/gp: c1 => [sd se]. 
move: (cleT c2 se); rewrite (card_card (CS_pow x b)) => sg.
case: (oleT_ee oa (Os_ordinal oy sd)) => //.
move /ocle1 => /(cpow_Meqle xnz); rewrite cpowcr => l3.
by move: (clt_leT sc (cleT sg l3)) => [].
Qed.

Lemma cpow_less_ec_pr7 x y z (p := (x ^<c y) ^c z):
  infinite_c y -> \2c <=c x ->
  [/\  ( \1c <=c z -> z <c \cf y -> p =  x ^<c y),
    (\cf y <=c z -> z <c y ->  p =  x ^c y) &
    (y <=c z  ->  p =  x ^c z)].
Proof.
move => icy x2.
have ia:= (cpow_less_ec_pr0 icy x2).
have ca := proj1 ia.
have aux: forall z, infinite_c z -> \cf z <=c z.
  move =>t icz;move: (icz) => [cz _]; move:(cz) => [oz _].
  apply: ocle3 => //; first by apply: CS_cofinality. 
  by apply: cofinality_pr3.
have cfys := (aux _ icy).
case: (p_or_not_p (exists a, cpow_less_ec_prop x y a)).
  move => [a ha];  split.
  - move=> z1 z2.
    have znz: z <> \0c by  move/cge1P:z1 => [_ /nesym].
    have hb:= (cpow_less_ec_pr2 ha x2).
    have pb:= (clt_leT z2 cfys).
    have cz := (proj31_1 z2).
    rewrite /p.
    case: (finite_or_infinite cz) => fz.
      have zN: natp z by apply /NatP.
      by rewrite (cpow_inf ia zN znz).
    have [b [b1 b2 b3]]: exists b, [/\ a <=c b, z <=c b & b <c y].
      move: ha => [ay _]; move: (ay) => [[ca1 _] _ _].
      case: (cleT_ee ca1 cz) => le1.
        by exists z;  split => //; apply: cleR.
      exists a; split;fprops.
    have ib:=(cle_inf_inf fz b2).
    by rewrite /p (hb _ b1 b3) - cpow_pow (cprod_inf b2 ib znz).
  - move => pa pb.
    have sy: singular_cardinal y.
      by split => //;  move: (cle_ltT pa pb) => [_].
    move: (cpow_less_ec_pr3 ha x2 sy) => [pc pd].
    rewrite /p pd - cpow_pow (cprod_inf (proj1 pb) icy) //.
    move: (cofinality_infinite_cardinal icy) => i1.
    exact: (infinite_nz (cle_inf_inf i1 pa)).
   - move => yz.
     move: (cpow_less_ec_pr2 ha x2) => hb.
     move: ha => [ay _];move: (ay) => [[oa _] _ _].
     case: (equal_or_not a \0c) => az.
      have y1: \1c <c y by apply: (clt_fin_inf finite_1 icy).
       move: cle_01; rewrite - az => ab.
       rewrite /p (hb _ ab y1) (cpowx1 (proj32 x2)) //.
     rewrite /p (hb _ (cleR oa) ay) - cpow_pow (cprodC).
     have iz:= (cle_inf_inf icy yz).
     by rewrite (cprod_inf (cleT (proj1 ay) yz) iz az).
move => ha.
have hb:= (cpow_less_ec_pr6 icy x2 ha).
move: (cpow_less_ec_pr5 icy x2 ha) => [X].
set Y := Lg (domain X) (fun z0 : Set => x ^c Vg X z0).
move => [q1 q2 q3 q4 q5].
have fgY: fgraph Y by rewrite /Y; fprops.
have q6: cardinal_fam Y by rewrite /Y; hnf;aw;move => t td; rewrite LgV//; fprops.
have q10: csum Y = x ^<c y.
  have pa: infinite_c (union (range Y)) by rewrite q5.
  have pb: cardinal (domain Y) <=c union (range Y).
    rewrite  q5 in pa.
    have pb := aux _ pa. 
    by rewrite q5 /Y; aw; rewrite q1 -hb (card_card (proj31 pb)).
  by rewrite (csum_of_small_b4 fgY q6 pa pb) q5.
have xx: \1c <=c z -> z <c \cf y -> p = x ^<c y.
  move => z1 zcy.
  rewrite -hb in zcy.
  have znz: z <> \0c  by  move/cge1P:z1 => [_ /nesym].
  rewrite /p (infinite_power7 ia zcy znz) /csumb.
  set T := Lg _ _.
  have pa: (forall i, inc i (domain T) -> Vg T i <=c x ^<c y).
     rewrite /T; aw => i id; rewrite LgV//.
     move: id => /(cardinals_ltP ca) => le2.
     have csr: cardinal_set (range Y).
       by move => t /(range_gP fgY) [w wi ->]; apply: q6.
     move: le2; rewrite - {1} q5 => le2.
     move: (clt_sup csr le2); move => [v ].
     move /(range_gP fgY); rewrite /Y;aw; move => [w wdx ->];rewrite LgV// => /proj1 le3.
     case: (equal_or_not i \0c) => iz.
       rewrite iz (cpow0x znz); apply: (cle0x ca).
     move: (cpow_Mleeq z le3 iz); rewrite - (cpow_pow) => pb.
     apply (cleT pb); apply: (cpow_less_pr2).
     move: (q2 _ wdx) => le1.
     rewrite hb in zcy; move: (clt_leT zcy cfys) => le4.
     by apply: cprod_inf5.
  have ct: cardinal_fam T by  rewrite /T; hnf;aw; move => a ad;rewrite LgV; fprops.
  have ct': fgraph T by  rewrite /T; fprops.
  have dt: domain T = cardinals_lt (x ^<c y) by rewrite /T; aw.
  move: (csum_of_small_b1 (conj ct' pa)).
  rewrite dt - cprod2cr.
  move: (infinite_power7d ca (infinite_nz ia)).
  set t := cardinal _; move=> [le2 tnz].
  have snz: csum T <> \0c.
    have zt: inc \1c (domain T). 
      rewrite /T;aw; apply /(cardinals_ltP ca).
      apply: (clt_fin_inf finite_1 ia).
    move: (csum_increasing6 (ct _ zt) zt).
    move: zt; rewrite {1}/T; aw => zt;rewrite {1} /T; rewrite LgV//.
    by rewrite cpow1x;  move/cge1P => [_ /nesym].
  rewrite (cprod_inf le2 ia tnz) => le3.
  by rewrite cprodC  (cprod_inf le3 ia snz).
case: (equal_or_not y omega0) => yo.
  split => //.
    by move:regular_omega => [ra rb];rewrite  yo rb => l1 /(cleNgt l1).
  move => yz;rewrite /p yo.
  have oic:= CIS_omega.
  have o2:=(cle_fin_inf finite_2 oic).
  rewrite yo in yz.
  have icz: infinite_c z by apply: (cle_inf_inf oic yz).
  case: (finite_or_infinite (proj32 x2)) => fx.
    rewrite (cpow_less_pr5c x2 fx).
    rewrite (infinite_power1_a o2 yz icz).
    by rewrite (infinite_power1_a x2 (cle_fin_inf fx icz) icz).
  by rewrite (cpow_less_pr5e fx).
have xnz:= (card_ge2_nz x2).
have pa: forall z,  infinite_c z -> (x ^<c y) ^c z <=c
    x ^c (csum (Lg (domain X) (fun t => (Vg X t) *c z))).
  move => w wi;  rewrite - q10.
  have pb: (forall i, inc i (domain Y) -> \2c <=c Vg Y i).
    rewrite /Y; aw => i idx; rewrite LgV//.
    move: (q4 yo _ idx) => enz.
    exact: (cleT x2 (cpow_Mle1 (proj32 x2) enz)).
  have le1 := (compare_sum_prod1 fgY pb).
  have le0: csum Y <> \0c by rewrite q10; apply: infinite_nz.
  apply: (cleT  (cpow_Mleeq w le1 le0)).
  rewrite (cpow_prod _ Y) cpow_sum /Y. 
  rewrite /cprodb.
  rewrite !Lgd; set f1 := Lg _ _; set f2 := Lg _ _.
  have ->: f1 = f2  by apply: Lg_exten => t te; rewrite !LgV// - cpow_pow.
  apply: cleR; rewrite /cprod; fprops.
move: (cofinality_infinite_cardinal icy) => cyi.
split => //.
  move => p1 p2.
  have icz: (infinite_c z) by apply: (cle_inf_inf cyi p1).
  move: (pa _ icz);  set f := Lg _ _ => pb.
  have pc: csum f <=c y.
    have df: domain f = \cf y by rewrite /f; aw; ue.
    have cf0: fgraph f by rewrite /f; fprops.
    have cf2: (forall i, inc i (domain f) -> Vg f i <=c y).
      rewrite /f; aw => i idx; rewrite LgV//; rewrite cprodC.
      apply: (cprod_inf4 (proj1 p2) (proj1 (q2 _ idx)) icy).
    move: (csum_of_small_b1 (conj cf0 cf2)).
    by rewrite df (cprod_inf cfys icy (infinite_nz cyi)).
  apply:cleA; first by apply: (cleT pb (cpow_Meqle xnz pc)).
  rewrite /p (cpow_less_pr6 icy x2); 
  apply: (cpow_Meqle (infinite_nz ia) p1).
move => p1.
have icz: (infinite_c z) by apply: (cle_inf_inf icy p1).
move: (pa _ icz); set f := Lg _ _ => p2.
have pb:  x ^c csum f <=c x ^c z.
  apply: (cpow_Meqle xnz).
  have cf1: fgraph f by rewrite /f; fprops.
  have cf2: (forall i, inc i (domain f) -> Vg f i <=c z).
    rewrite /f; aw => i idx; rewrite LgV//; rewrite cprodC.
    apply: cprod_inf1 => //.
    exact (cleT (proj1 (q2 _ idx)) p1).
  have df: domain f = \cf y by rewrite /f; aw; ue.
  move: (csum_of_small_b1 (conj cf1 cf2))=> l3; apply:(cleT l3).
  rewrite  df; exact: (cprod_inf1 (cleT cfys p1) icz). 
apply: (cleA (cleT p2 pb)).
exact: (cpow_Mleeq z (cpow_less_pr5a (proj32 x2) (infinite_ge2 icy)) xnz). 
Qed.

(** inaccessible cardinals *)

Lemma inaccessible_pr2 x:  inaccessible_w x ->
  cardinal (Zo x regular_cardinal) = x.
Proof.
move=> ix; move: ix (inaccessible_pr1 ix) => [rx [n ln xv]] xx.
have cx: cardinalp x by apply: (proj1 (proj1 rx)).
rewrite - {2}  (card_card  cx).
apply: cleA; first by apply: sub_smaller; apply Zo_S.
set S := (Zo x regular_cardinal).
have ox:= proj1 cx.
have lx: limit_ordinal x.
   suff : x = n by move => ->.
   apply:aleph_inj => //; [ by move: ln => [] | by ue].
have oo:= OS_aleph ox.
have pa: forall i, inc i x -> inc (\aleph (osucc i)) S.
    move=> i ix; apply: Zo_i. 
     rewrite xx; apply /(oltP oo); apply: aleph_lt_lto.
     by  apply/(oltP ox); move: lx => [_ _ ]; apply.
   apply: regular_initial_successor; apply: (Os_ordinal ox ix).
set f := Lf (fun z => (\aleph (osucc z))) x S.
have inf: injection f.
  apply: lf_injective => // u v ux vx sv.
  have ou:= (Os_ordinal ox ux).
  have ov :=(Os_ordinal ox vx).
  apply: osucc_inj => //; apply: aleph_inj; fprops.
have ->: x =  source f by rewrite /f; aw.
have ->: S =  target f by rewrite /f; aw.
by apply: inj_source_smaller.
Qed.


Definition next_dominant x :=
  the_least_fixedpoint_ge (cpow \2c) x.
Definition card_dominant x:=
   infinite_c x /\ forall a b, a <c x -> b <c x -> a ^c b <c x.

Lemma card_dominant_pr1 x: cardinalp x ->
   x <> \0c -> (forall m, m <c x -> \2c ^c m <c x) -> card_dominant x.
Proof.
move=> cx xnz h.
have ix: infinite_c x.
  case: (finite_or_infinite cx) => // fx.
  have xN: natp x  by apply /NatP.
  move: (cpred_pr xN xnz) => [pa pb].
  have pc: (cpred x) <c x by rewrite {2} pb; apply: cltS.
  move: (h _ pc); rewrite {2} pb; move /(cltSleP pa) => h1.
  case: (cleNgt h1 (cantor (proj32 h1))).
split => //.
move=> a b ax bx.
case: (equal_or_not b \0c) => bz.
   rewrite bz cpowx0; apply: clt_fin_inf => //.
   rewrite /NatP; fprops.
case: (equal_or_not a \0c) => az.
   rewrite az cpow0x // ; apply: clt_fin_inf => //.
   rewrite /NatP; fprops.
have [c [ca cb ccx]]: exists c, [/\ a <=c c, b <=c c & c <c x].
  have ca:= proj31_1 ax.
  have cb:= proj31_1 bx.
  case: (cleT_ee ca cb); [ exists b; split |  exists a;split ]; fprops.
have h1 : a ^c b <=c c ^c c by apply: cpow_Mlele.
apply (cle_ltT h1).
case: (finite_or_infinite (proj31_1 ccx)) => fc.
   apply: clt_fin_inf => //. 
   by apply /NatP; apply NS_pow; apply /NatP.
by rewrite (infinite_power1_b fc); apply h.
Qed.

Lemma card_dominant_pr2: card_dominant omega0.
Proof.
have io: infinite_c omega0 by rewrite - aleph0E; apply: CIS_aleph; fprops.
split => //.
have lo: forall c, c <c omega0 <-> natp c.
   move=> c; split => h.
     by apply /olt_omegaP; apply: oclt.
   by apply: clt_fin_inf => //; apply /NatP.
move=> a b /lo aN /lo bN; apply/lo; fprops.
Qed.


Lemma next_dominant_pr x (y:= next_dominant x): cardinalp x ->
   [/\ card_dominant y ,  x <c y &
   (forall z,  card_dominant z -> x <c z -> y <=c z)].
Proof.
move => cx; rewrite /y /next_dominant; clear y.
rewrite /the_least_fixedpoint_ge. 
move: (induction_defined_pr (cpow \2c) x).
set f := induction_defined _ _; move=> [sf [ff sjf f0 fnz]].
have cs1: forall n, natp n -> cardinalp (Vf f n).
   apply: Nat_induction; first ue.
   move=> n nN _; rewrite (fnz _ nN) /cpow; fprops.
have cs: cardinal_set (target f).
  by move => t /sjf; rewrite sf; move=> [u ub ->]; apply: cs1.
set y:= \osup (target f).
have ltxy: x <c y. 
  apply (clt_leT (cantor cx)); apply: (card_sup_ub cs).
  rewrite - f0 - (fnz _ NS0); Wtac; rewrite sf; apply:NS_succ; fprops.
split => //.
  apply: card_dominant_pr1 => //; first by apply: (CS_sup cs).
  move => yz; rewrite yz in ltxy; case: (clt0 ltxy).
  move=> m my.
  have [n pd pe]: exists2 n, inc n (target f) & m <=c n.
    ex_middle bad.
    have cm:= proj31_1 my.
    have pd: forall t, (inc t (target f) -> t <=c m).
      move=> t ti.
      case: (cleT_ee (cs _ ti) cm) => // b1; case: bad;ex_tac.
    case: (cltNge my (card_ub_sup cm pd)).
  move: (sjf _ pd) => [u us uv].
  have le1: \2c ^c m <=c  \2c ^c n by apply: cpow_Meqle; fprops.
  have le2: \2c ^c n <c  \2c ^c ( \2c ^c n).
    apply: cantor; rewrite /cpow; fprops.
  apply: (cle_ltT le1); apply: (clt_leT le2).
  apply (card_sup_ub cs); aw; rewrite sf in us.
  rewrite uv - (fnz _ us) - (fnz _ (NS_succ us)); Wtac; rewrite sf.
  rewrite -/(natp _);fprops.
move=> z [iz dz] xz; apply card_ub_sup; first by exact (proj1 iz).
move => a /sjf; rewrite sf; move=> [n nB ->].
suff : Vf f n <c z by  move=> [].
move: n nB; apply: Nat_induction; first by ue.
move=> n nB le1; rewrite (fnz _ nB); apply: dz => //.
apply: clt_fin_inf => //; rewrite /NatP; fprops.
Qed.


Lemma card_dominant_pr3 x (y := next_dominant x) :
  cardinalp x -> \2c ^c y  =  y ^c omega0.
Proof.
move =>  cx; move:  (next_dominant_pr cx); rewrite -/y.
move=> [[iy yp] _].
move: (iy) => [cy _ _].
have oy: omega0 <=c y by apply /infinite_c_P2.
have co:= CS_omega.
apply: cleA; last first.
  rewrite -(infinite_power1_b iy).
  apply:cpow_Mlele; fprops;  by apply: infinite_nz.
move: (induction_defined_pr (cpow \2c) x) => /=.
set f := (induction_defined (cpow \2c) x).
move => [qa [rb qb2] qc qd].
have bv: y = \osup (target f) by done.
have ra: fgraph (Lg omega0 (Vf f)) by fprops.
have bv1: y = \osup (range (Lg omega0 (Vf  f))).
  rewrite bv; apply: f_equal; set_extens t.
    move /qb2=> [u usf ->]; apply /(range_gP ra); aw.
    rewrite qa in usf;exists u => //; rewrite LgV//.
  move /(range_gP ra); aw; move => [u usf ]; rewrite LgV//; move => ->; Wtac; ue.
have rd0: forall u, natp u ->  cardinalp (Vf f u).
   apply: Nat_induction; first ue.
   move=> n nN _; rewrite (qd _ nN) /cpow; fprops.
have rd: cardinal_fam (Lg omega0 (Vf f)) by hnf; aw => t tw;rewrite LgV; fprops.
have bv2: y = csum (Lg omega0 (Vf f)).
  by rewrite csum_of_small_b4 // - bv1 // Lgd  (card_card co).
rewrite {1} bv2 cpow_sum Lgd - cprod_of_same.
have cs1: (cardinal_set (target f)).  
  by move => t /qb2 [u usf ->];apply: rd0; rewrite /natp - qa.
apply: cprod_increasing; aw; trivial => t tN; rewrite !LgV//. 
by rewrite -(qd _ tN); apply: (card_sup_ub cs1); Wtac;rewrite qa; apply:NS_succ.
Qed.

Definition least_non_trivial_dominant := next_dominant omega0.

Lemma card_dominant_pr4 (b:=  least_non_trivial_dominant):
  [/\ card_dominant b,
    omega0 <c b,
    (forall z, card_dominant z -> omega0 <c z -> b <=c z),
    (b ^c omega0 = omega0 ^c b)
    &   (b ^c omega0 = \2c ^c b) /\
    (b ^c omega0 = (\2c ^c b) ^c b) ].
Proof.
have co:= CS_omega.
move: (next_dominant_pr co) (card_dominant_pr3 co). 
rewrite (_: (next_dominant omega0) = b ) //.
move => [pa pb pc] pd; move: (pa) => [pf _].
have io: infinite_c omega0 by rewrite - aleph0E; apply: CIS_aleph; fprops.
have pe: omega0 ^c b = \2c ^c b.
   apply: infinite_power1_a => //.
   apply: cle_fin_inf;fprops.
   apply: (proj1 pb).
by rewrite - cpow_pow (csquare_inf pf) pe pd. 
Qed.


Lemma dominant_limit a: ordinalp a -> 
  ~ (card_dominant (\aleph (osucc a))).
Proof.
move=> oa [cd1 cd2].
set x := \omega a.
rewrite - (cnextE oa) in cd2.
move: (CIS_aleph oa) => icx.
move: (cnext_pr2 (proj1 icx))(cnext_pr3 (proj1 icx)) => lt1 pa.
by move: (cd2 _ _ lt1 lt1); rewrite (infinite_power1_b icx) => /cltNge.
Qed.

Lemma card_dominant_pr5 x: card_dominant x ->
  (\2c ^<c x = x /\ \2c ^c x = gimel_fct x).
Proof.  
move => [icx cdx].
suff pa: \2c ^<c x = x. 
  split; [ by exact | by rewrite (cpow_less_pr6a icx) pa ].
move: (icx) => [cx _].
have aux:= (@cpow_less_pr0 \2c x).
apply: cleA.
  apply:card_ub_sup => //i /funI_P [z zi ->].
  have pa:=(clt_fin_inf finite_2 icx).
  move: zi => /(cardinals_ltP cx) pb.
  exact (proj1 (cdx _ _ pa pb)).
by case: (cpow_less_compare icx).
Qed.


(* x is y-strong *)

Definition rel_strong_card x y:= 
   forall t, t <c x -> t ^c y <c x.

Lemma card_dominant_pr7 a (A := \aleph a) B
  (s := \osup (fun_image a (fun z=> \aleph z ^c B))):
  rel_strong_card A B -> B <> \0c -> ordinalp a -> 
  (s <=c A /\ (limit_ordinal a -> s = A)).
Proof.
move => sab bnz oa.
have cA:= (CS_aleph oa).
move: (CIS_aleph oa); rewrite -/A => iA.
have pa: s <=c A.
  apply: card_ub_sup => // i /funI_P [z za ->].
  have lt1: \omega z <c A. 
     by apply: aleph_lt_ltc; move: za =>  /oltP [].
  exact: (proj1 (sab _ lt1)).
split => // la.
set g := (fun z => \omega z ^c B).
set f := (fun z  => \omega z).
have pb: (forall x, inc x a -> f x <=c g x).
  move => x xa; rewrite /f/g.
  have ox:= Os_ordinal oa xa.
  apply: (cpow_Mle1 (CS_aleph ox) bnz).
apply: cleA; first by exact.
apply: cleT (card_sup_image pb).
move: aleph_normal => [_ h]; move: (h _ la).
have ->: (fun_image a \omega) = (fun_image a f) by set_extens t; aw.
move => <-; apply: cleR; apply: (CS_aleph oa).
Qed.

Lemma card_dominant_pr8 a b  (A := \aleph a) (B:= \aleph b) (X := A ^c B):
  ordinalp a -> ordinalp b -> rel_strong_card A B ->
    ( (B <c \cf A -> X = A) /\ (\cf A <=c B -> X = gimel_fct A)).
Proof.
move => oa ob sab.
move: (CIS_aleph oa)  (CIS_aleph ob) => ia ib.
move: (infinite_power9 ia ib) => [_ _ i9]; exact (i9 sab).
Qed.

Definition the_nondominant_least A B :=
  select (fun z => [/\ z <c A , A <=c z ^c B  &
    (forall t, t <c A -> A <=c t ^c B -> z <=c t)]) A.

Lemma the_nondominant_least_pr1 A B (C:= the_nondominant_least A B):
  ~ (rel_strong_card A B) -> cardinalp A ->
  [/\ C <c A, A <=c C ^c B  &
    (forall t, t <c A -> A <=c t ^c B -> C <=c t)].
Proof.  
move => h cA.
rewrite /C/the_nondominant_least.
apply select_pr; last first.
  move => x y p1 [p2 p3 p4] q1 [q2 q3 q4].
  exact: (cleA (p4 _ q2 q3) (q4 _ p2 p3)).
pose p c := c <c A /\  A <=c c ^c B.
have [c cp]: exists c, p c.
   ex_middle h1; case: h.
   move => u ua.
   have cp: cardinalp (u ^c B) by fprops.
   case: (cleT_el (proj32_1 ua) cp) => // h2.
   case: h1; exists  u; rewrite /p;split => //.
have oc: ordinalp c by move: cp => [[[[cx _] _] _] _].
move: (least_ordinal4 oc cp);set z :=  least_ordinal _ _.
move=> [_ [p1 p2] p3].
have iaa: inc z A.
   by move: (oclt p1) => /oltP0 [_ _].
ex_tac;split => // => t ta le. 
have pt: (p t) by split.
have ot: ordinalp t by move: pt => [[[[cx _] _] _] _].
move: (ocle1 (p3 _ ot pt)).
rewrite (card_card (proj31_1 p1)).
by rewrite (card_card (proj31_1 (proj1 pt))).
Qed.


Lemma the_nondominant_least_pr2 a b  (A := \aleph a) (B:= \aleph b) 
   (c := (ord_index (the_nondominant_least A B))):
  ~ (rel_strong_card A B) -> ordinalp a -> ordinalp b ->
   (A <=c \2c ^c B) \/
  [/\ c <o a, A <=c \aleph c ^c B  &
    (forall t, t <o a -> A <=c \aleph t ^c B -> c <=o t)].
Proof.
move => h oa ob.
move: (the_nondominant_least_pr1 h (CS_aleph oa)).
set C := the_nondominant_least A B; move => [pa pb pc].
have cc:= proj31_1 pa.
case: (finite_or_infinite cc) => ifc.
  left.
  have bnz: B <> \0c by apply: aleph_nz.
  have iB:= (CIS_aleph ob).
  have cp:= (CS_pow \2c B).
  case: (equal_or_not C \0c) => cnz.
    move: pb; rewrite cnz (cpow0x bnz) => le2.
    exact: (cleT le2 (cle0x cp)).
  case: (equal_or_not C \1c) => cno.
    move: pb; rewrite cno cpow1x => le2.
    exact: (cleT le2 (cge1 cp  (@cpow_nz _ B card2_nz))).
  have c2:= (cge2 cc cnz cno).
  have le1: C <=c B by apply: cle_fin_inf.
  have <- //: C ^c B = \2c ^c B by apply: infinite_power1_a.
right.
move: (ord_index_pr1 ifc); rewrite {1 2}/C -/c; move => [oc ac].
have ltca: c <o a by apply aleph_ltc_lt => //; rewrite ac.
rewrite ac; split => //.
move => t ta tb.
have lt1: \aleph t <c A by apply: aleph_lt_ltc.
move: (pc _ lt1 tb); rewrite -ac; apply: (aleph_lec_le oc (proj31_1 ta)).
Qed.

Lemma card_dominant_pr9 A B C:
   infinite_c B ->  C <c A ->  A <=c C ^c B -> A ^c B = C ^c B.
Proof.
move =>  ib ca le1.
case: (equal_or_not C \0c) => cnz.
  move: le1; rewrite cnz (cpow0x (infinite_nz ib)) => az.
  case: (clt0 (clt_leT ca az)).
have anz: A <> \0c.
  move=> h; rewrite h in ca; case: (clt0 ca).
move: (cpow_Mleeq B le1 anz). 
rewrite - cpow_pow (csquare_inf ib) -/B => le4.
exact: (cleA le4 (cpow_Mleeq B (proj1 ca) cnz)).
Qed.

Lemma card_dominant_pr10 a b  (A := \aleph a) (B:= \aleph b) (X := A ^c B)
  (C := (the_nondominant_least A B)):
  ordinalp a -> ordinalp b ->
  \2c ^c B <c X -> ~ (rel_strong_card A B) -> 
  [/\ rel_strong_card C B, singular_cardinal C,
    \cf C <=c B, B <c C & X = gimel_fct C].
Proof.
move => oa ob lt2 nsr.
move: (CIS_aleph oa) (CIS_aleph ob) => ia ib.
move: (the_nondominant_least_pr1 nsr (proj1 ia)).
rewrite -/C; move => [pa pb pc].
move: (card_dominant_pr9 ib pa pb); rewrite -/A -/B -/C => eq1.
have na2b: ~(A <=c \2c ^c B).
  move => bad.
  move: (cpow_Mleeq B bad (aleph_nz oa)). 
  by rewrite - cpow_pow (csquare_inf ib) => /(cltNge lt2).
have cc:=(proj31_1 pa).
case: (cleT_el cc (proj1 ib)) => lBC.
  case: na2b.
  have cp := (CS_pow \2c B).
  case: (equal_or_not C \0c) => cnz.
    move: pb; rewrite cnz (cpow0x  (aleph_nz ob)) => le2.
    exact: (cleT le2 (cle0x cp)).
  case: (equal_or_not C \1c) => cno.
    move: pb; rewrite cno cpow1x => le2.
    exact: (cleT le2 (cge1 cp  (@cpow_nz _ B card2_nz))).
  by rewrite - (infinite_power1_a (cge2 cc cnz cno) lBC ib).
have pd:rel_strong_card C B.
  move => t tC.
  case: (cleT_el cc (CS_pow t B)) => // cb.
  move: (card_dominant_pr9 ib tC cb); rewrite -/B => le1.
  rewrite le1 in pb.
  case: (cltNge tC (pc _ (cle_ltT (proj1 tC) pa) pb)).
have ic: infinite_c C by apply: (cle_inf_inf ib (proj1 lBC)).
move: (ord_index_pr1 ic); set c:= (ord_index C); move => [oc qb].
rewrite -qb in  pd.
move: (card_dominant_pr8 oc ob pd); rewrite qb -/B; move => [pe pf].
rewrite qb in  pd.
case: (cleT_el (CS_cofinality (proj1 cc)) (proj1 ib)) => h.
  move: (cle_ltT h lBC) => [_ ne].
  by rewrite  - (pf h) - eq1. 
by move: pb; rewrite (pe h) => /(cltNge pa).
Qed.

Lemma card_dominant_pr11 A B (X := A ^c B):
  infinite_c A -> infinite_c B -> 
  [\/ X = A, X =  \2c ^c B |
  exists C, [/\ infinite_c C, rel_strong_card C B,
    \cf C <=c B , B <c C & X = gimel_fct C]].
Proof.
move => ia ib.
move: (ord_index_pr1 ia); set a:= (ord_index A); move => [oa qa].
move: (ord_index_pr1 ib); set b:= (ord_index B); move => [ob qb].
case: (equal_or_not (\2c ^c B) (A ^c B)) => eq0; first by constructor 2.
have pa: \2c ^c B <c A ^c B. 
  split => //; apply: (cpow_Mleeq B (infinite_ge2 ia) card2_nz).
case: (cleT_el (proj1 ia) (proj1 ib)) => cab.
  constructor 2; exact :(infinite_power1_a (infinite_ge2 ia) cab ib).
case: (p_or_not_p (rel_strong_card A B)) => sr.
  move: (card_dominant_pr8 oa ob); rewrite qa qb => h.
  move: (h sr) => [h1 h2].
  have cco:=(CS_cofinality (proj1 (proj1 ia))).
  case: (cleT_el cco (proj1 ib)) => h3.
    constructor 3; exists A;split;fprops.
  by constructor 1 ; apply: h1.
move: (card_dominant_pr10 oa ob).
set C := the_nondominant_least _ _; rewrite qa qb.
move => xx; move: (xx pa sr); move => [q1 q2 q4 q5 q6].
constructor 3; exists C; split => //.
apply (cle_inf_inf ib (proj1 q5)).
Qed.

Definition inaccessible x :=
   inaccessible_w x /\ (forall t, t <c x -> \2c ^c t <c x).

Definition cprod_of_small f x:=
  [/\ cardinal_fam f,
  (forall i, inc i (domain f) -> Vg f i <c x) &
  domain f <c x].

Lemma inaccessible_dominant x: inaccessible x -> card_dominant x.
Proof.
move => [[pa1 pa2] pb]. 
move: pa2 => [n [on _ _] xv].
move: (CIS_aleph on); rewrite - xv => icx.
apply: (card_dominant_pr1 (proj1 icx) (infinite_nz icx) pb).
Qed.

Lemma inaccessible_pr3 x: \2c <c x ->
   (forall f, cprod_of_small f x -> cprod f <c x) ->
   card_dominant x.
Proof.
move => cx h.
have ccx := proj32_1 cx.
apply: card_dominant_pr1 => //.
   move => p; rewrite p in cx; case: (clt0 cx).
move => m mx; rewrite - cprod_of_same; apply: h; hnf; aw; split => //.
  hnf;aw => t te; rewrite LgV; fprops.
by move => t te; rewrite LgV. 
Qed.

Lemma inaccessible_pr4 x: \2c <c x ->
   (forall f, cprod_of_small f x -> cprod f <c x) ->
   (x = omega0 \/ (exists2 n, limit_ordinal n & x = \aleph n)).
Proof.
move=> x2 h.
move: (inaccessible_pr3 x2 h) => [pa pb].
move: (ord_index_pr1 pa) => [on xv]; rewrite -xv.
case: (ordinal_limA on) => ln; last by right; exists (ord_index x).
  left; rewrite ln; apply: aleph0E.  
move: ln => [m om mv].
move: (cnext_pr1 (CS_aleph om)). 
rewrite (cnextE om) - mv xv; move => [pc pd pe].
move: (pb _ _ pd pd); rewrite (infinite_power1_b (CIS_aleph om)).
rewrite - {1} xv mv => /(aleph_pr10a om) => l2.
case: (cleNgt l2 (cantor (proj31_1 pd))).
Qed.

Lemma inaccessible_pr5 x: \2c <c x ->
   (forall f, cprod_of_small f x -> cprod f <c x) ->
   (x = omega0 \/ inaccessible x).
Proof.
move=> h1 h2.
case: (inaccessible_pr4 h1 h2) => lx; first by left.
move: (inaccessible_pr3 h1 h2) => [pa pb].
right; split; last by move => t tx; apply: pb.
split => //; split => //.
have H:=(cofinality_card pa).
rewrite H;ex_middle cs.
have pe: \cf x <c x  by split => //; exact (cofinality_small pa).
move: (cofinality_c_pr3 pa) =>[f [[qa qb] df sf etc]].
have cff: cardinal_fam f by move => t /qb /proj31_1.
have: cprod_of_small f x by split => //; rewrite  df H.
move /h2 => l2.
by move: (compare_sum_prod1 qa etc); rewrite sf => /(cltNge l2).
Qed.


Lemma inaccessible_pr6 x:  inaccessible x ->
   (forall f, cprod_of_small f x -> cprod f <c x).
Proof.
move => [[[cx rx] pb] pc] f [pe pf pg].
set z := domain f in pg.
set f' := (Lg z (Vg f)).
have df' : domain f' = z by rewrite /f'; aw.
have pa: csum_of_small1 x f'.  
  by rewrite /f';split; fprops;hnf; aw => i idf; rewrite LgV//; apply: pf.
have cff: cardinal_fam f' by move => t /(proj2 pa) /proj31_1.
set su := csum f'.
have sux: su <=c x.
  move: (csum_of_small_b2 pa); rewrite df' => qb.
  exact: (cleT qb (cprod_inf1 (proj1 pg) cx)).
case: (equal_or_not su x) => sux1.
  have: cofinality_c x <=o z.
    move: (cofinality_c_rw (infinite_ge2 cx)) => [_ _ cfxp].
    by apply: (cfxp _ (proj1 (proj31_1 pg))); exists f'.
  by move: (oclt pg); rewrite rx => qa /(oltNge qa).
have dx:card_dominant x.  
  apply: card_dominant_pr1 => //; [ exact: (proj32 sux) | by apply infinite_nz].
apply: cle_ltT ((proj2 dx) _ _ (conj sux sux1) pg).
rewrite - cprod_of_same; apply cprod_increasing;rewrite /cst_graph; aw; trivial.
move => i idf; rewrite LgV//.
have udf': inc i (domain f') by ue.
move: (csum_increasing6 (cff _ udf') udf'); rewrite  LgV//.
Qed.

Lemma inaccessible_pr7 x y:  inaccessible x ->
  y <> \0c -> y <c x ->  x ^c y = x.
Proof.
move => [[[icx cfx] pb] pc] pd pe.
rewrite (cofinality_card icx) in cfx.
rewrite - cfx in pe. 
move: (icx) => [cx _].
rewrite (infinite_power7 icx pe pd) /csumb.
set f := Lg _ _.
have snz: csum f <> \0c.
  suff: \1c <=c csum f by move/cge1P =>[_ /nesym].
  have zi: inc \1c (cardinals_lt x).
    by apply /(cardinals_ltP cx); apply: infinite_gt1.
  have zi1: inc \1c (domain f) by rewrite /f; aw.
  move: CS1.
  have <-: Vg f \1c = \1c by rewrite/f LgV// cpow1x.
  by move => cc;apply:(csum_increasing6 cc zi1).
rewrite cprodC; apply: (cprod_inf) => //.
have dx:card_dominant x.  
  by apply: card_dominant_pr1 => //; apply infinite_nz.
rewrite cfx in pe.
have pf: csum_of_small1 x f.
  rewrite /f;split; fprops; hnf;  aw; move => i idf; rewrite LgV//.
  by move: idf => /(cardinals_ltP cx) => idf;apply (proj2 dx).
move: (csum_of_small_b2 pf) => le1.
have df: cardinal (domain f) <=c x. 
  rewrite Lgd.
  by case: (infinite_power7d cx (infinite_nz icx)).
by move: (cprod_inf1 df icx);rewrite cprod2cr; apply: cleT.
Qed.


Lemma inaccessible_pr8 x:  inaccessible x -> x = x ^<c x.
Proof.
move => h; move: (h) => [[[pa1 pa2] pb] pc]; move:  (proj1 pa1) => cx.
apply: cleA.
 by move: (cpow_less_pr2 x (infinite_gt1 pa1)); rewrite (cpowx1 cx).
apply: card_ub_sup => // t /funI_P [z z1 ->].
move: z1 => /(cardinals_ltP cx) => z1.
case: (equal_or_not z \0c) => xnz.
  rewrite xnz cpowx0; apply (proj1 (infinite_gt1 pa1)).
move: (inaccessible_pr7 h xnz z1) => ->.
apply: (cleR (proj32_1 z1)).
Qed.

Lemma inaccessible_dominant1 x: 
   card_dominant x -> 
   (x = omega0 \/ (exists2 n, limit_ordinal n & x = \aleph n)).
Proof.
move => [pa pb].
move: (ord_index_pr1 pa); set c := ord_index x; move => [pd pe].
case: (ordinal_limA pd) => ln;last by right; exists c.
  by left; rewrite -pe ln aleph0E.
move: ln => [m om mv].
set y:= \aleph m.
have yx: y <c x.
  by  rewrite /y -pe; apply: aleph_lt_ltc; rewrite mv; apply: oltS.
move: (pb _ _ yx yx); rewrite (infinite_power1_b (CIS_aleph om)) => le1.
by move: (cnext_pr3(CS_aleph om));rewrite (cnextE om) -mv pe => /(cltNge le1).
Qed.


Lemma inaccessible_dominant2 x 
  (p1 := forall z, \0c <c z -> z <c x -> x ^c z = x)
  (p2:= forall z, \0c <c z ->  x ^c z = x *c \2c ^c z):
  [/\ (infinite_c x -> p1 -> p2),
    (card_dominant x -> (p1 <-> p2)),
    (card_dominant x -> p1 -> (x = omega0 \/ inaccessible x)) &
    (x = omega0 \/ inaccessible x -> (card_dominant x /\ p1))].
Proof.
have r1:infinite_c x -> p1 -> p2.
  move=> icx hp1 z zp.
  have x2:= (infinite_ge2 icx).
  have xnz:=(infinite_nz icx).
  have cz:= proj32_1 zp.
  case: (cleT_ee (proj1 icx) (CS_pow \2c z)) => le1.
    have icp:= (cle_inf_inf icx le1).
    case: (finite_or_infinite cz) => icz.
      have f1: finite_c (\2c ^c z). 
        by apply /NatP; apply NS_pow; fprops.
      case: (finite_not_infinite f1 icp). 
    rewrite (infinite_power1 x2 le1 icz).
    by rewrite cprodC cprod_inf.
  have pnz: \2c ^c z <> \0c by apply: cpow2_nz.
  rewrite (hp1 _ zp (clt_leT (cantor cz) le1)).
  rewrite cprod_inf //.
have r2: card_dominant x -> (p1 <-> p2).
  move=> [icx cdx]; split; first by apply: r1.
  move => hp2 z z0 zx.
  have pnz: \2c ^c z <> \0c by apply: cpow2_nz.
  move: (cdx _ _ (clt_fin_inf finite_2 icx) zx) => [l1 _].
  rewrite (hp2 _ z0) cprod_inf //.
have r3:  card_dominant x -> p1 -> x = omega0 \/ inaccessible x.
  move => pa pc; case: (inaccessible_dominant1 pa); first by left.
  move => h; right.
  move: pa => [pa pb].
  split; last first. 
    by move => t tx; apply: pb => //; apply: (clt_fin_inf finite_2 pa).
  split; last by exact.
  have h1:= (cofinality_c_small (proj1 pa)).
  split => //; ex_middle eq1.
  have pd: \0c <c cofinality_c x. 
    apply: (clt_fin_inf  finite_0 (cofinality_infinite pa)).
  move: (power_cofinality (infinite_ge2 pa)).
  by rewrite (pc _ pd (conj h1 eq1)); move => [_].
split => //.
case => ix.
  rewrite ix; split; first by apply: card_dominant_pr2.
  move => z z0 zf.
  have pa: infinite_c x by rewrite ix; apply: CIS_omega.
  have pb: natp z by rewrite ix in zf; move:(oclt zf) => /oltP0 [_ _].
  have pc: z <> \0c by  move: z0 => [_] /nesym.
  by rewrite cpow_inf.
split; first by apply: inaccessible_dominant.
by move => z [_ /nesym zc] zx;apply: inaccessible_pr7.
Qed.

Lemma inaccessible_dominant3 x: omega0 <c x ->
  (inaccessible x <->
  ( (forall a b, a <c x -> b <c x -> a ^c b <c x)
    /\ (forall z, \0c <c z -> z <c x -> x ^c z = x))).
Proof.
move => [h1 h2].
have ix: infinite_c x by  apply /infinite_c_P2.
move: (inaccessible_dominant2 x) => [pa pb pc pd]; split.
  move => h; move: (pd (or_intror h)) => [[_ pe] pf]; split => //.
move => [h3 h4].
by case: (pc (conj ix h3) h4) => // eq; move: h2; rewrite eq.
Qed.


Lemma cofinality_sum1 a: ordinalp a -> 
   \cf (\aleph(a +o omega0)) = omega0.
Proof.
move => oa.
rewrite (regular_initial_limit1 (osum_limit oa omega_limit)).
rewrite (cofinality_sum oa olt_0omega).
exact (proj2 regular_omega).
Qed.

Lemma cofinality_sum2 a: ordinalp a ->  
   singular_cardinal (\aleph(a +o omega0)).
Proof.
move => oa; move: (OS_sum2 oa OS_omega) => os.
split; first by apply: CIS_aleph.
rewrite (cofinality_sum1 oa) - {1} aleph0E => h.
symmetry in h; move: (aleph_inj os OS0 h) => /(osum2_zero oa OS_omega) [_].
by move: omega_nz.
Qed.

Lemma singular_non_collectivizing: 
  not (exists E, forall x, singular_cardinal x -> inc x E).
Proof.
move=> [E ep].
set F := Zo E singular_cardinal.
have ce: cardinal_set F by move => t /Zo_P [_ [[pa _] _]].
move: regular_initial_limit4 => h.
have ef: inc (\aleph omega0) F by  apply: Zo_i => //; apply: ep.
move: (cle_inf_inf (CIS_aleph OS_omega) (card_sup_ub ce ef)) => ins.
move: (ord_index_pr1 ins) =>[]; set n := ord_index _ => on yv.
have h1:= (cofinality_sum2 on).
have xf: inc  (\aleph (n +o omega0))  F by apply: Zo_i => //; apply: ep.
move: (card_sup_ub ce xf); rewrite -yv => h2.
move: (aleph_lec_le (OS_sum2 on OS_omega) on h2).
by move: (osum_Meqlt olt_0omega on); rewrite (osum0r on) => pa /(oltNge pa).
Qed.

Lemma genconthypothesis_alt b: ordinalp b ->
  (forall a, ordinalp a -> \2c ^c (\aleph a) = \aleph (a +o b)) ->
  b <o omega0.
Proof.
move => ob h.
have oo:= OS_omega.
case: (oleT_el oo ob) => // lob.
pose p x := b <o x +o b. 
have pb: p b. 
  have pa: \0o <o omega0 by apply ordinal_finite3; fprops;apply emptyset_finite.
  move: (osum_Meqlt (olt_leT pa lob) ob); rewrite osum0r //.
move: (least_ordinal4 ob pb); set a :=  least_ordinal p b.
move => [oa pa al].
have ab: a <=o b by apply: al.
have a0: \0o <o a.
  move: pa; rewrite /p - {1} (osum0l ob); apply: (osum_Mlteqr OS0 oa ob).
have paa : a <o a +o a by move: (osum_Meqlt a0 oa); rewrite osum0r.
case: (ordinal_limA oa) => nz; first by case: (proj2 a0).
  move: nz => [m om mv].
  have pm: p m. 
    move: OS1 pa; rewrite /p mv => o1.
    rewrite - osucc_pr // - osumA // osum_1inf //.
  by move: (al _ om pm); rewrite mv; move/(oltNge (oltS om)). 
set k := \aleph (a +o a).
have oaa:=(OS_sum2 oa oa).
have sk: singular_cardinal k.
  split; first by apply:CIS_aleph.
  have laa:= (osum_limit oa nz).
  have anz: a <> \0o by apply: limit_nz.
  rewrite /k (regular_initial_limit1 laa) (cofinality_sum oa a0).
  move=> bad; move: (cofinality_pr3 oa); rewrite bad.
  move: (aleph_pr6 oaa) => le1 le2.
  case: (oltNge paa (oleT le1 le2)). 
set s1 := \aleph (a +o b).
have pc : forall c, c<o a -> \2c ^c (\aleph (a +o c)) = s1.
  move => c ca.
  have oc:= proj31_1 ca.
  have oac: ordinalp (a +o c) by apply: OS_sum2 => //.
  rewrite (h _ oac) - (osumA oa oc ob).
  have <- //: b = (c +o b).
    ex_middle neq.
    have p1: b <=o c +o b by apply osum_M0le.
    case: (oltNge ca (al _ oc (conj p1 neq))).
have pd: forall c, a<=o c -> c<o a +o a ->  \2c ^c (\aleph c) = s1.
  move=> c ac caa; move: (odiff_pr ac) => [qa qb].
  rewrite qb in caa; move: (osum_Meqltr qa oa oa caa) => da.
  by move: (pc _ da); rewrite -qb.
have px:  (cpow_less_ecb k).
   exists (\aleph a); first by apply: (aleph_lt_ltc paa).  
   move=> c c1 c2.
   move: (cle_inf_inf (CIS_aleph oa) c1) => ic.
   move: (ord_index_pr1 ic) => [om mv].
  rewrite (pd _ (oleR oa) paa).
  rewrite  -mv in c1 c2.
  have p1:= (aleph_lec_le oa om  c1).
  have p2:= (aleph_ltc_lt om oaa c2).
  by rewrite -mv  (pd _ p1 p2).
move: (cpow_less_pr10 sk px); rewrite (h _ oaa).
set s2 := \aleph ((a +o a) +o b) => eq1.
have c12: s1 <c s2. 
  apply: aleph_lt_ltc; rewrite - osumA //; apply: osum_Meqlt => //.
suff: \2c ^<c k <=c s1 by rewrite - eq1 => /(cltNge c12).
apply:card_ub_sup; first exact: (proj31_1 c12).
move => i /funI_P [z zv ->].
have ck: cardinalp k by move: sk => [[ok _] _].
move: zv => /(cardinals_ltP ck) zv.
have cz:=proj31_1 zv.
have is1: infinite_c s1 by apply: CIS_aleph; apply: OS_sum2.
case: (finite_or_infinite cz) => fz.
  apply: cle_fin_inf => //.
  by apply /NatP; apply: NS_pow; fprops; apply /NatP.
move: (ord_index_pr1 fz)=> [om zv1].
have lt1: (ord_index z) <o a +o a.
   by apply: (aleph_ltc_lt om oaa); rewrite zv1 -/k.
rewrite - zv1.
case: (oleT_ee oa om) => le1.
  by rewrite (pd _ le1 lt1);  apply: cleR; move: is1 => [].
by rewrite (h _ om); apply: aleph_le_lec; apply: osum_Mleeq.
Qed.


Section GenContHypothesis_Props.

Hypothesis gch: GenContHypothesis.

Lemma infinite_power10 x y (z := x ^c y): infinite_c x ->
  [/\  (y = \0c -> z = \1c),
   (y <> \0c -> y <c \cf x -> z = x),
   (\cf x <=c  y -> y <=c x -> z = cnext x)&
   (x <c y -> z = cnext y)].
Proof.
move=> ic; rewrite /z.
have x2:= (infinite_ge2 ic).
have cx:= proj1 ic.
have xx:=(cleR cx).
have xnz:= infinite_nz ic.
have r1: y = \0c -> x ^c y = \1c by move => ->; rewrite cpowx0.
have r2: x <c y -> x ^c y = cnext y.
  move=> [xy _].
  have icy:(infinite_c y) by apply: (cle_inf_inf ic xy).
  rewrite (gch icy); apply: (infinite_power1_a _  xy icy).
  apply: cle_fin_inf => //; rewrite /NatP; fprops.
move: (cnext_pr1 cx) => [qa qb qc].
have r3: \cf x <=c y -> y <=c x -> x ^c y = cnext x.
  move=> pa pb.
  move: (power_cofinality x2); rewrite (cofinality_card ic) => pc.
  have pd: x ^c (\cf x) <=c x ^c y by apply: cpow_Mlele.
  have lt1:= (qc _ (clt_leT pc pd)).
  apply: cleA lt1.
  rewrite (gch ic) - (infinite_power1_b ic).
  by apply: cpow_Mlele.
split => //  ynz ycx.
have cy := (proj31_1 ycx).
have yl1:=(cge1 cy ynz).
apply: cleA; last by apply: cpow_Mle1.
rewrite (infinite_power7 ic ycx ynz) /csumb.
set f := Lg _ _.
have cf: cardinal_fam f by rewrite /f;hnf;aw => a ac;rewrite LgV //; fprops.
have fl:  forall i, inc i (domain f) -> Vg f i <=c x.
  rewrite /f; aw; move=> i id; rewrite LgV//.
  case: (equal_or_not i \0c) => iz.
    rewrite iz (cpow0x ynz); apply: cle0x;  fprops.
  case: (equal_or_not i \1c) => io.
    rewrite io (cpow1x); apply: cle_fin_inf => //; apply: finite_1.
  move: id => /(cardinals_ltP cx) lt.
  have ci:= proj31_1 lt.
  case: (Nat_dichot cy) => yN.
    case: (Nat_dichot ci) => iN.
      by apply: (cle_fin_inf _ ic); apply /NatP;apply: NS_pow. 
    exact: (cleT (cpow_inf1 iN yN) (proj1 lt)).
  have ra: forall t, infinite_c t -> t <c x -> \2c ^c t <=c x.
    move=> t it tx. 
    by rewrite - (gch it); move: (cnext_pr1 (proj1 it))=> [ _ _]; apply.
  have ray:  \2c ^c y <=c x.
    by apply: ra => //; apply: (clt_leT ycx); apply: cofinality_small.
  case: (Nat_dichot ci) => iN.
    have b1:= NS1.
    have iy: i <=c y by apply (Nat_le_infinite).
    have i2: \2c <=c i.
      rewrite - succ_one ; apply /(cleSltP b1).
      by split; [apply: cge1  | apply:nesym].
    rewrite (infinite_power1_a i2 iy yN) //.
  have i2:= (cle_fin_inf finite_2 iN).
  case: (cleT_ee ci cy) => cp1.
    rewrite (infinite_power1_a i2 cp1 yN) //.
  have le1:  i ^c y  <=c i ^c i by apply: cpow_Mlele => //; fprops.
  apply: (cleT le1).
  rewrite (infinite_power1_b iN); exact: (ra _ iN lt).
have df: domain f = (cardinals_lt x) by rewrite /f; aw.
move: (infinite_power7d cx xnz)=> [pe pf].
have fgf: fgraph f by rewrite /f; fprops.
move: (csum_of_small_b1 (conj fgf fl)).
rewrite  Lgd - (cprod2cr)(cprod_inf pe ic pf) => aux.
by apply cprod_inf4.
Qed.

Lemma infinite_power10_a x: infinite_c x ->
   x ^c (\cf x) = cnext x.
Proof.
move => icx; move: (infinite_power10 (\cf x) icx) => [_ _ pa _].
have h:=(cofinality_small icx).
apply: pa => //;apply (cleR (proj31 h)).
Qed.

Lemma infinite_power10_b x y:
  infinite_c x -> y <c  (\cf x) -> y <> \0c -> 
  x ^c y = x.
Proof.
move=> icx yc ynz.
by move:  (infinite_power10 y icx) => [_ pb _ _]; apply: pb.
Qed.

Lemma cpow_less_pr11a x y: 
  infinite_c y -> \2c <=c x -> finite_c x ->
  x ^<c y = y.
Proof.
move => icy x2 xf.
have cy := proj1 icy.
have cs:= (@cpow_less_pr0 y x).
have le1: x ^<c y <=c y.
  apply: card_ub_sup => // i /funI_P [z /(cardinals_ltP cy) zs ->].
  have cz:=proj31_1 zs.
  case: (finite_or_infinite cz) => fz.
    apply: cle_fin_inf => //.
    by apply /NatP; apply: NS_pow; fprops; apply /NatP.
  rewrite (infinite_power1_a x2 (cle_fin_inf xf fz) fz).
  rewrite - (gch fz).
  by move: (cnext_pr1 cz) => [_  _ ]; apply.
ex_middle neq.
move: (cpow_less_pr2 x (conj le1 neq)); set t := (x ^<c y) => le2.
move: (cleT (cpow_Mleeq t x2  card2_nz) le2) => le3.
case: (cleNgt le3(cantor (proj32 le3))).
Qed.


Lemma cpow_less_pr11b x: infinite_c x -> \2c ^<c  x = x.
Proof. move => icx; apply: cpow_less_pr11a;fprops. Qed.


Lemma cpow_less_pr12 x: regular_cardinal x -> 
  x ^<c  x = x.
Proof.
move => /regular_cardinalP [ix cx]; move: (ix) => [cax _].
have aux: x ^c \1c = x by rewrite cpowx1.
have x1:=(infinite_gt1 ix).
apply: cleA; last by  rewrite - {1} aux; apply  cpow_less_pr2.
apply: (card_ub_sup cax) => i.
move /funI_P => [z] /(cardinals_ltP cax)  zx ->.
case: (equal_or_not z \0c) => zz.
  by rewrite zz cpowx0; move: x1 => [].
rewrite (infinite_power10_b); fprops; ue. 
Qed.

Lemma inaccessible_weak_strong x:
   inaccessible_w x -> inaccessible x.
Proof.
move => h; split => // t th.
move: h => [[pa pb] [n [on _ ln xv]]].
case: (finite_or_infinite (proj31_1 th)) => it.
  apply:(clt_fin_inf) => //. 
  apply /NatP; apply: NS_pow; apply /NatP;fprops.
move: th; rewrite - (gch it).
move: (ord_index_pr1  it) => [om <-]; rewrite (cnextE om) xv => le1.
move: (aleph_ltc_lt om on le1) => mn.
apply: aleph_lt_ltc; apply /oltP0; split;fprops.
apply: ln; apply /oltP => //.
Qed.

Lemma inaccessible_pr8_gch x: \2c <c x ->
   ([\/ (x = omega0),
     (exists2 n, ordinalp n & x = \aleph (osucc n)) | inaccessible x]
   <-> x = x ^<c x).
Proof.
move => x2.
set p:= (exists2 n, ordinalp n & x = \aleph (osucc n)).
have cx:=proj32_1 x2.
have xnz : x <> \0c.
  move => xz; rewrite xz in x2; case: (clt0 x2).
have xp:=(clt_ltT clt_02 x2).
have aux: p -> x = x ^<c x.
  move => [n on xv].
  rewrite {3} xv; move: (cpow_less_pr4 xp (CIS_aleph on)).
  rewrite (cnextE on); move => ->.
  have i1:=(CIS_aleph on).
  by rewrite xv - (cnextE on) (gch i1) - cpow_pow (csquare_inf).
split.
   case =>//; first by move ->; symmetry; apply: cpow_less_pr5f. 
   by apply: inaccessible_pr8.
move => h. 
case: (finite_or_infinite cx) => fx.
  have xN: natp x by apply /NatP.
  move: (cpred_pr xN xnz)=>  [ub uv].
  move: (cpow_less_pr3 xp ub); rewrite -uv -h.
  move: (cltS ub); rewrite -uv => pa.
  have xp1: \1c <c cpred x.
    by apply/(cltSSP CS1 (proj31_1 pa)); rewrite - uv succ_one.
  move: (cpow_Meqlt xN ub  xp1 (cle_ltT (proj1 xp1) pa)).
  by rewrite (cpowx1 cx); move => [].
move: (ord_index_pr1 fx) => [om xv]; symmetry in xv.
case: (ordinal_limA om) => ln.
    by constructor 1; rewrite - aleph0E - ln.
  move: ln => [n on nv]; constructor 2; exists n => //.
   by rewrite -nv. 
constructor 3;apply: inaccessible_weak_strong.
split; last by exists (ord_index x).
split => //; ex_middle cs.
have cs1:=(cofinality_c_small (proj1 fx)).
move: (cpow_less_pr2 x (conj cs1 cs)); rewrite -h => lt1.
case: (cleNgt lt1(power_cofinality (proj1 x2))).
Qed.

Lemma infinite_power7h_rev x: \0c <c x ->  
  (forall y, \0c <c y ->
  x ^c y =  (csumb (cardinals_lt x) (fun z => z ^c y)) *c x)
  -> regular_cardinal x. 
Proof.
move => xp h.
move: (xp) => [_ /nesym xnz].
have cx:=proj32_1 xp.
case: (equal_or_not x \1c) => x1.
  move: (h _ (clt_02)); rewrite x1 cpow1x; rewrite x1 in xp.
  have ->: (cardinals_lt \1c) = singleton \0c.
     apply : set1_pr; first  by apply /(cardinals_ltP CS1).
     by move => t /(cardinals_ltP CS1) /clt1.
  rewrite csum_trivial3 (cpow0x card2_nz) (card_card CS0) cprod0l. 
  by move => /card1_nz.
case: (equal_or_not x \2c) => x2.
  move: (h _ (clt_02)); rewrite x2; rewrite x2 in xp.
  have ->: (cardinals_lt \2c) =  C2.
      set_extens t.
        move => aux; apply /set2_P; apply: clt2.
        by apply /(cardinals_ltP CS2).
     case /set2_P => ->; apply /(cardinals_ltP CS2);
        [apply: clt_02 | apply: clt_12].  
  rewrite csum2_pr0 cpowx2 cprod_22 cpow1x (cpow0x card2_nz) (csum0l CS1).
  rewrite  (cprod1l CS2) => eq3.
    by case: (proj2 (clt_leT (cltS NS2) (proj1 (cltS NS3)))).
case: (Nat_dichot cx) => fx.
  move: (h _ (clt_01)); rewrite (cpowx1 cx) /csumb; set f := Lg _ _ => pb.
  have pa: \2c <=c csum f.
    have xx: inc \2c (cardinals_lt x).
      by apply /(cardinals_ltP cx); split; [ apply: cge2 | apply:nesym].
    have i2d: inc \2c (domain f) by rewrite/f; aw.
    move: CS2;have ->: \2c = Vg f \2c by rewrite/f LgV// (cpowx1 CS2).
    move => cc; exact:(csum_increasing6 cc i2d).
  move: (cprod_Mlele pa (cleR cx)); rewrite -pb - csum_nn => qb.
  by move: (csum_Mlteq fx  xp);rewrite (csum0l cx) => /(cleNgt qb).
have H:= (cofinality_card fx).
split => //.
move: (cofinality_infinite fx); rewrite H => coi.
move: (h _ (clt_fin_inf finite_0 coi)). 
rewrite /csumb; set f :=  Lg _ _.
rewrite (infinite_power10_a fx) => pa.
ex_middle cnx.
have pc:= (cofinality_small fx).
have pb: forall i, inc i (domain f) -> Vg f i <=c x.
  rewrite /f;aw;move=> i idf; rewrite LgV//.
  move: idf => /(cardinals_ltP cx) => idf.
  case: (equal_or_not i \0c) => i0.
     rewrite i0 cpow0x; [ exact (proj1 xp) |  by apply: infinite_nz ].
  case: (equal_or_not i \1c) => i1.
    by rewrite i1 cpow1x; apply (proj1 (infinite_gt1 fx)).
  have y2:= (cge2 (proj31_1 idf) i0 i1).
  have aux: forall z, infinite_c z -> z <c x -> \2c ^c z <=c x.
    move => z iz zx; rewrite - (gch iz).
     by move: (cnext_pr1 (proj1 iz)) => [_  _]; apply.
  case: (cleT_ee (proj31_1 idf) (proj31 pc)) => le1.
    by rewrite (infinite_power1_a y2 le1 coi); apply: aux.
  have iy:= (cle_inf_inf coi le1).
  move: (cpow_Meqle i0 le1); rewrite (infinite_power1_b iy) => ce.
  apply: (cleT ce (aux _ iy idf)).
have cff:  fgraph f by rewrite /f; fprops.
move: (csum_of_small_b1 (conj cff pb)).
rewrite Lgd.
move: (infinite_power7d cx xnz) => [ca _].
move: (cprod_Mlele (cleR cx) ca); rewrite cprod2cr => cb cc.
move: (cleT cc cb); rewrite (csquare_inf fx) => cd.
move: (cprod_Mlele cd (cleR cx)); rewrite (csquare_inf fx) - pa.
by move: (cnext_pr1 cx) => [_ aa _ ]=> /(cltNge aa).
Qed.


Lemma infinite_increasing_power5gch X 
  (Y:= Lg (domain X) (fun z => \aleph (Vg X z)))
  (a := \osup (range X)):
  ofg_Mlt_lto X -> limit_ordinal (domain X) -> 
  ((cprod Y) = \aleph a ^c (cardinal (domain X)) /\ 
   (cprod Y) = \aleph (osucc a)).
Proof.
move => pa pb.
move: (infinite_increasing_power5 pa pb).
move: (increasing_sup_limit4 pa pb);rewrite -/Y -/a; move => [pc pd pe].
have ia:=(CIS_aleph (proj31 pc)).
rewrite -/a -/Y.
rewrite - (cnextE (proj31 pc)) - (gch ia).
move: (cnext_pr1 (proj1 ia)) => [_].
set A := \omega a; set B := A ^c cardinal (domain X).
move=> _ qa [qb qc qd].
have qe:= (qa _ qb).
have bv := (cleA qc (cleT qd qe)).  
by split => //; apply:cleA => //; rewrite bv.
Qed.


Lemma cpow_less_ec_pr8 x y ( z := x ^<c y):
  infinite_c y -> infinite_c x ->
  [/\ (y <=c \cf x ->  z = x),
   (\cf x <c y -> y <=c cnext x ->  z = cnext x) &
  (cnext x <c y -> z = y)].
Proof.
move => icy  icx; rewrite /z.
have cy:= proj1 icy.
have cx:= proj1 icx.
have sp1:=(cnext_pr2 cx).
have sp1' := proj1 sp1.
split.
    move => pa; move: (cpow_less_pr5a cx (infinite_ge2 icy)) => le1.
    apply: cleA; last by exact.
    apply: (card_ub_sup cx)  => i /funI_P [t ta ->]; move: ta. 
    move/ (cardinals_ltP cy) => ty. 
    move: (clt_leT ty pa) => lt2.
    case: (equal_or_not t \0c) => tnz.
      rewrite tnz cpowx0; apply: (cle_fin_inf finite_1 icx).
    rewrite (infinite_power10_b icx  lt2 tnz); fprops.
  move => p1 p2;  apply: cleA; last first.
    by move: (cpow_less_pr2 x p1); rewrite (infinite_power10_a icx).
  apply: (card_ub_sup (proj32 p2)) => i /funI_P [t ta ->]; move: ta. 
  move /(cardinals_ltP cy) => ty. 
  move: (infinite_power10 t icx) => [pa pb pc pd].
  case: (equal_or_not t \0c) => tz.
    rewrite (pa tz); apply: cleT p2.
    apply: (cle_fin_inf finite_1 icy).
  case: (cleT_el (proj31_1 p1) (proj31_1 ty)) => ctc.
    rewrite (pc ctc (cnext_pr4 cx (clt_leT ty p2))); exact:(cleR (proj32 p2)).
  by rewrite (pb tz ctc).
move => qa.
apply: cleA.
  apply: (card_ub_sup cy).
  move => i /funI_P [t ta ->]; move: ta. 
  move /(cardinals_ltP cy) => ty. 
  move: (infinite_power10 t icx) => [pa pb pc pd].
  case: (equal_or_not t \0c) => tz.
    by rewrite (pa tz); apply: (cle_fin_inf finite_1 icy).
  move: (cofinality_small icx) => p1.
  case: (cleT_el (proj31 p1) (proj31_1 ty)) => ctc.
    case: (cleT_el (proj31_1 ty) cx) => ctx.
      rewrite (pc ctc ctx); apply: (proj1 qa).
    rewrite (pd ctx); move: (cnext_pr1 (proj32_1 ctx)).
    by move => [_  _]; apply.
  by rewrite (pb tz ctc); apply: (cleT sp1' (proj1 qa)).
move: (ord_index_pr1 icy); set c := (ord_index y); move => [qb qc].
move: (ord_index_pr1 icx); set d := (ord_index x); move => [qd qe].
move: (qa); rewrite - {1} qe -qc (cnextE qd) => qa1.
move: (aleph_ltc_lt (OS_succ qd) qb qa1) => qa2.
case: (ordinal_limA qb) => ln.
    rewrite ln in qa2;case: (olt0 qa2).
   move:ln => [e oe se]. 
   move: (cnextE oe); rewrite - se => <-.
   move: (CIS_aleph oe) => icz.
   rewrite (cpow_less_pr4 (clt_fin_inf finite_0 icx) icz).
   move: (infinite_power10 ( \omega e) icx) => [ra rb rc rd].
   have xe: x <c \omega e.
     by rewrite -qe; apply: aleph_lt_ltc; apply /oltSSP; ue.
   by rewrite (rd xe); apply: cleR; rewrite (cnextE oe) - se qc. 
rewrite {1} (proj2 (aleph_normal) _ ln).
apply: card_ub_sup; first by apply: CS_cpow_less.
move => i /funI_P [w wi ->].
have wc: w <o c by apply /oltP.
move: (aleph_lt_ltc wc) => le1.
apply: cleT (cpow_less_pr2 x le1). 
apply: (cleT (proj1 (cantor (proj31_1 le1)))).
apply: (cpow_Mleeq (\omega w) (infinite_ge2 icx) card2_nz).
Qed.

End GenContHypothesis_Props.

Definition beth x :=
  let p := fun z => \2c ^c z in
  let osup := fun y f => \osup (fun_image y (fun z => (p (f z)))) in 
  let osupp:= fun f =>  Yo (domain f = \0o) omega0 (osup (domain f) (Vg f)) in
  let  f:= transdef_ord osupp in
  f x.

Lemma beth_prop:
  [/\ normal_ofs beth, beth \0o = omega0 & 
   (forall x,  ordinalp x -> beth (osucc x) = \2c ^c (beth x)) ].
Proof.
apply: normal_ofs_existence.
- move => x ox.
  move: (CS_pow \2c x) => cp.
  case: (oleT_el (proj1 cp) ox) => //.
  move /ocle1; rewrite (card_card cp) => /cleNgt; case.
  by move: (cantor (CS_cardinal x)); rewrite cpowcr.
- move => x y /ocle1 /(cpow_Meqle card2_nz).
  rewrite cpowcr cpowcr; apply: ocle.
- apply: OS_omega.
Qed.

Lemma beth0: beth \0o = omega0.
Proof. by move: (beth_prop) => [_ pa _]. Qed.

Lemma beth_succ x: ordinalp x ->
    beth (osucc x) = \2c ^c (beth x).
Proof.  move: (beth_prop) => [_ _ ]; apply. Qed.

Lemma beth_normal: normal_ofs beth.
Proof. by  move: (beth_prop) => [pa _ _ ]. Qed.

Lemma CS_beth x: ordinalp x -> cardinalp (beth x).
Proof. 
move: (beth_prop) => [pa pb pc] ox.
case: (least_ordinal6 (fun z => cardinalp (beth z)) ox) => //.
set y := least_ordinal _ _;move=> [pd pe]; case.
case: (ordinal_limA pd).
- move ->; rewrite pb; apply: CS_omega.
- move => [z oz za]; rewrite za pc; fprops. 
- by move /(proj2 pa) => ->; apply: CS_sup => t /funI_P [z zy ->]; apply: pe.
Qed.

Lemma beth_M x y: x <o y -> beth x <c beth y.
Proof.
move: (proj1 beth_normal) => pa ineq.
exact: (oclt3 (CS_beth (proj31_1 ineq))(CS_beth (proj32_1 ineq)) (pa _ _ ineq)).
Qed.

Lemma beth_pr1 x: ordinalp x -> infinite_c (beth x).
Proof.
move => ox; case: (ozero_dichot ox).
  move => ->; rewrite beth0; apply CIS_omega.
by move /beth_M; rewrite beth0; move => [/infinite_c_P2 le1 _].
Qed.

Lemma beth_gch: GenContHypothesis <->  beth =1o \aleph.
Proof.
split; last first.
  move => h x icx.
  move: (ord_index_pr1 icx) => [oy <-].
  by rewrite (cnextE oy) - (h _ oy) - (beth_succ oy) (h _ (OS_succ oy)).
move =>h x ox.
case:(least_ordinal6 (fun z => beth z = \aleph z) ox) => //.
set y := least_ordinal _ _; move =>[pa pb];case.
case: (ordinal_limA pa).
- by move => ->; rewrite aleph0E beth0.
- move=> [u ou u1]. 
  rewrite u1 (beth_succ ou) - (cnextE ou) (h _ (CIS_aleph ou)).
  rewrite pb // u1; fprops.
move=> lt.
rewrite (proj2 beth_normal _ lt)  (proj2 aleph_normal _ lt).
by apply: ord_sup_2funI => s st; apply: pb.
Qed.

Lemma beth_fixed_point x: 
   ordinalp x -> beth x = x -> card_dominant x.
Proof.
move => ox bfx.
have  icx: infinite_c x by rewrite -bfx; apply: beth_pr1.
have xnz:= (infinite_nz icx).
have cx := proj1 icx.
apply: card_dominant_pr1 => // m mx.
have cm:= proj31_1 mx.
move: (infinite_card_limit2 icx) => lx; move: (lx) =>[qa qb qc].
have [b pa pb]: exists2 b, m <=c beth b & b <o x.
  ex_middle bad.
  have pc:forall i, inc i (fun_image x beth) -> i <=c m.
    move => t /funI_P [i ix ->].
    have oi:= Os_ordinal qa ix.
    case: (cleT_ee (CS_beth oi) cm) => // h; case: bad; exists i => //.
    by apply /oltP.
  have : union (fun_image x beth) <=c m.
    by apply: card_ub_sup.
  by rewrite - ((proj2 beth_normal) _ lx) bfx => /(cltNge mx).
apply: (cle_ltT (cpow_Meqle card2_nz pa)).
have ob:= proj31_1 pb.
rewrite -(beth_succ ob) - bfx; apply: beth_M.
by move: pb => /(oltP ox) hh; apply / (oltP ox);apply: qc.
Qed.


Lemma cofinality_least_fp_beth x y:
  beth x <> x ->  least_fixedpoint_ge beth x y ->
  cofinality y = omega0.
Proof. apply: (cofinality_least_fp_normal beth_normal). Qed.


Lemma aleph_and_beth a: ordinalp a -> 
   exists b, [/\ ordinalp b, beth b <=c \aleph a & \aleph a <c beth (osucc b)].
Proof.
move => oa; case: (normal_ofs_bounded (OS_aleph oa) (beth_normal)).
  by rewrite beth0 => /(oleNgt (aleph_pr5 oa)).
move => [y [oy ha hb]]. 
have hc:=(CS_aleph oa).
have hd:= (ocle3 (proj1 (beth_pr1 oy)) hc ha).
have he:= (oclt3 hc (proj1 (beth_pr1 (OS_succ oy))) hb).
by exists y. 
Qed.


Lemma beth_limit a: limit_ordinal a -> 
   exists2 b, limit_ordinal b & beth a = \aleph b.
Proof.
move => la.
have oa := proj31 la.
move/limit_ordinal_P:la => [ap al].
move: (ord_index_pr1 (beth_pr1 oa)); set b := ord_index _; move => [ob bv].
case: (ordinal_limA ob) =>lb.
- by case:(proj2 (beth_M ap)); move: bv; rewrite lb aleph0E - beth0.
- move:lb => [c oc cv].
  move:bv; rewrite cv => ea.
  move: (aleph_and_beth oc) => [d [od ha hb]].
  move: (cle_ltT ha (aleph_lt_ltc (oltS oc))); rewrite ea => la.
  case: (oleT_ell oa od) => lb.
     by case: (proj2 la); rewrite lb.
   by case : (cltNge la (proj1(beth_M lb))).
  case: (cltNge (beth_M (al _ (al _ lb)))).
  move: (cleT (aleph_pr12f oc) (cpow_M2le (proj1 hb))). 
  by rewrite ea - (beth_succ (OS_succ od)).
- by exists b.
Qed.



Lemma beth_inaccessible a k : inaccessible k ->
  a <o k -> beth a <c k.
Proof.
move => [ina inb] sb.
have oa:= (proj31_1 sb).  
move: sb.
case: (least_ordinal6 (fun a => a <o k -> beth a <c k) oa) => //.
set y:= least_ordinal _ _; move => [oy pb]; case => lyk.
case: (ordinal_limA oy).
- by move ->; rewrite beth0; move: (inaccessible_uncountable ina).
- move => [x ox yv]. 
  have xy: inc x y by rewrite yv; fprops.
  have lxk: x <o k by apply:olt_ltT lyk; move /(oltP oy): xy.
  rewrite yv (beth_succ ox); exact: (inb _ (pb _ xy lxk)).
- move => ly; rewrite (proj2 beth_normal _ ly). 
  have ck:=  (proj1 (proj1(proj1 ina))).
  move/(ocle2P ck (proj31_1 lyk)): (lyk) => cyk.
  have ha:=(cle_ltT (fun_image_smaller y beth) cyk).
  apply: (regular_sup (proj1 ina) ha) => i /funI_P [z zy ->].
  have lzy: z <o y by apply /(oltP (proj31 ly)).
  exact: (pb _ zy (olt_ltT lzy lyk)).
Qed.



Lemma beth_inaccessible1 k : inaccessible k -> beth k = k.
Proof.
move => ik.
move: beth_normal => [sa sb].
have infk:= (proj1 (proj1 (proj1 ik))).
have ck := (proj1 infk); have ok := (proj1 ck).
apply: cleA.
  rewrite (sb _ (infinite_card_limit2 infk)); apply:card_ub_sup => //.
  move => i /funI_P [z /(oltP ok) zk ->]. 
  exact: (proj1(beth_inaccessible ik zk)).
move:(ocle1 (osi_gex sa ok)). 
by rewrite (card_card ck) (card_card (CS_beth ok)).
Qed.


Lemma card_dominant_pr12 x: infinite_c x ->
  (forall m, infinite_c m -> m <c x -> \2c ^c m <c x) -> card_dominant x.
Proof.
move => icx ha; apply:(card_dominant_pr1 (proj1 icx) (infinite_nz icx)).
move => m lmx.
case: (finite_or_infinite (proj31_1 lmx)) => li; last by apply:ha.
by apply:clt_fin_inf icx; apply/NatP; apply:(NS_pow NS2); apply/NatP.
Qed.

Lemma beth_dominant a: limit_ordinal a -> card_dominant (beth a).
Proof.
move => la; have oa:= (proj31 la).
apply: (card_dominant_pr12 (beth_pr1 oa)).
move => m /ord_index_pr1; set c := ord_index _; move => [oc <- lt0].
move: (aleph_and_beth oc) => [b [ob lt1 lt2]].
move/limit_ordinal_P:la => [anz sa].
have lt3: b <o a.
  have la4:= (cle_ltT lt1 lt0).
  case: (oleT_ell oa ob) => //. 
    by move => ba; move: (proj2 la4); rewrite ba.
  move/beth_M => /cltNge; case; exact (proj1 la4).
move: (cpow_M2le (proj1 lt2)); rewrite - (beth_succ (OS_succ ob)) => sb.
by apply: (cle_ltT sb); apply:beth_M; apply: (sa); apply:sa.
Qed.

Lemma beth_dominantP x: infinite_c x ->
  (card_dominant x <-> exists2 a, (a = \0c \/ limit_ordinal a) & x = beth a).
Proof.
move => icx;split; last first.
   move => [a oa ->]; case: oa=> oa; last by apply:beth_dominant.
   by rewrite oa beth0; apply:card_dominant_pr2.
move/ord_index_pr1: icx; set c := ord_index _; move => [oc <- xd].
move:(aleph_and_beth oc) => [b [ob lt1 lt2]].
have lt4:= (clt_fin_inf finite_2 (proj1 xd)).
case: (equal_or_not (beth b) (\aleph c)) => eqa; last first.
   have lt3 : beth b <c \omega c by split.
   move: (proj2  xd _ _ lt4 lt3); rewrite - (beth_succ ob) => /cltNge; case.
   exact (proj1 lt2).
exists b => //; case: (ordinal_limA ob) => lb; [by left | | by right].
move: lb => [d od bv].
have lc: d <o b by rewrite bv; apply: (oltS od).
move: (beth_M lc); rewrite eqa => lt3.
by move: (proj2 (proj2  xd _ _ lt4 lt3)); rewrite -(beth_succ od) - bv eqa.
Qed.


Lemma beth_pow0 m:  m <c beth \0c -> m <> \0c ->
  (beth \0c) ^c m = beth \0c.
Proof.
rewrite beth0; move => /clt_omegaP mN mz. 
exact:(cpow_inf CIS_omega mN mz).
Qed.
   
Lemma beth_pow1 m: beth \0c <=c m ->
  (beth \0c) ^c m = \2c ^c m.
Proof.
rewrite beth0 => bm.
move/clt_omegaP:NS2 => [ha _].
by apply: (infinite_power1_a ha bm); apply/infinite_c_P2.
Qed.

Lemma beth_pow2 m a:  ordinalp a ->  m <=c beth a -> m <> \0c ->
  (beth (osucc a)) ^c m = beth (osucc a).
Proof.
move => oa lmb mz.
by rewrite (beth_succ oa) - cpow_pow (cprod_inf lmb (beth_pr1 oa) mz).
Qed.

Lemma beth_pow3 m a: ordinalp a -> beth a <=c m ->
  (beth (osucc a)) ^c m = \2c ^c m.
Proof.
move => oa lmb.
have ib:= (beth_pr1 oa).
have im:= cle_inf_inf ib lmb.
by rewrite (beth_succ oa) - cpow_pow cprodC (cprod_inf lmb im (infinite_nz ib)).
Qed.



Lemma beth_pow4c m a: limit_ordinal a -> (beth a) <=c m  ->
  (beth a) ^c m = \2c ^c m.
Proof.
move => sa sb. 
have ib := (beth_pr1 (proj31 sa)).
exact: (infinite_power1_a (infinite_ge2 ib) sb (cle_inf_inf ib sb)).
Qed.

(*

Lemma beth_pow4b m a: limit_ordinal a -> 
   \cf a <=c m -> m <=c (beth a)  ->
  (beth a) ^c m = \2c ^c (beth a) /\  (beth a) ^c m = m ^c (beth a).
Proof.
move => sa sb sc.
have ib := (beth_pr1 (proj31 sa)).
have icfa:= (cofinality_infinite_limit sa).
have im:= (cle_inf_inf icfa sb).
have r1:= (infinite_power1_a (infinite_ge2 im) sc ib).
suff: beth a ^c m = \2c ^c beth a by rewrite r1.
apply:cleA.
  by rewrite -(infinite_power1_b ib); apply:(cpow_Meqle (infinite_nz ib) sc).
have: exists X,
   fgraph X /\ domain X = \cf a /\ ofg_Mlt_lto X /\ a = union (range X).
   admit. (* conjecture *)
move => [X [fgX [dX [ iX srX]]]].
move: (infinite_prod4 sa sb dX iX srX).
admit. (* conjecture *)
Abort.

Lemma beth_pow4 m a: limit_ordinal a -> m <c \cf (beth a) -> m <> \0c ->
  (beth a) ^c m = beth a.
Proof.
move => oa lmb mnz.
move:beth_normal => [sa sb].
have bav:=(sb a oa). 
move:(beth_limit oa) => [b ob bbv].
have cf1: \cf (beth a) = \cf b 
   by move:(regular_initial_limit1 ob); rewrite - bbv.
admit. (* conjecture *)
Abort.

Lemma beth_monotone2 x: cardinalp x ->  x <=c (beth x).
Proof.
move => cx; apply: (ocle3 cx (CS_beth (proj1 cx))).
exact:(osi_gex (proj1 beth_normal) (proj1 cx)).
Qed.


Lemma beth_pow5a (x:= beth aleph0): 
  x ^c aleph0 = \2c ^c x /\  x ^c aleph0 = aleph0 ^c x.
Proof.
apply: beth_pow4b.
- apply: omega_limit.
- rewrite/aleph0 (proj2 regular_omega); apply:cleR; apply:CS_aleph0.
- apply:(beth_monotone2 CS_aleph0).
Qed.


Lemma beth_pow5b (x:= beth aleph1): x ^c aleph0 = x.
Proof.
apply: beth_pow4.
- apply: aleph_limit; apply OS1.
- have ->: \cf beth aleph1 =  \cf aleph1.
    admit.  (* conjecture *) 
  move:regular_cardinal_aleph1 => [s1 s2].
  rewrite -(cofinality_card  s1) s2 /aleph0 - aleph0E.
  exact: (aleph_lt_ltc olt_01).
- apply:omega_nz.
Qed.


Lemma beth_pow5c (x:= beth aleph1): 
  x ^c aleph1 = \2c ^c x /\  x ^c aleph1 = aleph1 ^c x.
Proof.
apply: beth_pow4b.
- apply: aleph_limit; apply OS1.
- move:regular_cardinal_aleph1 => [s1 s2].
  rewrite -(cofinality_card  s1) s2; apply:(cleR (proj1 s1)).
- apply:beth_monotone2; apply:(CS_aleph OS1).
Qed.

*) 

Definition SingCardHypothesis:=
  forall x, infinite_c x ->  \2c ^c (\cf x) <c x ->
       x ^c (\cf x) = cnext x.
 
Lemma sch_gch: GenContHypothesis -> SingCardHypothesis.
Proof.  
move => gch x ix pa.
have pb:= (cofinality_small ix).
move: (infinite_power10 gch (\cf x) ix); move => [_ _ pc _].
apply: pc => //; apply: (cleR (proj31 pb)).
Qed.

Lemma SCH_case1 x: infinite_c x -> \2c ^c (\cf x) <> x.
Proof.
move => icx eq1.
move: (cofinality_infinite_cardinal icx) => ic.
by move: (power_cofinality2 ic); rewrite  eq1; move => [_].
Qed.

Lemma SCH_prop2 x (p:= cpow_less_ecb x):
   singular_cardinal x -> SingCardHypothesis ->
   ( (p -> \2c ^c x = \2c ^<c x)
    /\ (~ p -> \2c ^c x = cnext (\2c ^<c x))).
Proof.
move => sc sch; split; first by apply: cpow_less_pr10.
move => pf.
have aux: forall a, a <c x -> 
  exists b, [/\ a <=c b, b <c x & \2c ^c a <c \2c ^c b].
  move => a ax; ex_middle ba1.
  case: pf; exists a => //; move => b b1 b2.
  have le1:= (cpow_Meqle card2_nz b1).
   by ex_middle ne1; case: ba1; exists b.
have  le22: \2c <=c \2c by fprops.
move: sc => [ix sx].
have pf':~ (exists a : Set, cpow_less_ec_prop \2c x a).
  by move => [a [px py]]; case: pf; exists a.
move: (cpow_less_ec_pr6 ix le22 pf') => eq1.
have pa: (\2c ^c (\cf (\2c ^<c x))) <c \2c ^<c x.
  have pb:= (cofinality_small ix).
  move: (aux _ (conj pb sx)) => [b [p1 p2 p3]].
  by rewrite eq1; apply: (clt_leT p3); apply: cpow_less_pr2.
rewrite (cpow_less_pr6a ix) - eq1.
exact (sch _ (cpow_less_ec_pr0 ix le22) pa).
Qed.

Lemma SCH_prop3 x y (z := x ^c y): infinite_c x -> \1c <=c y ->
  SingCardHypothesis ->
  ( (x <=c \2c ^c y  -> z =  \2c ^c y)
    /\ ((\2c ^c y <c x) ->
      (  (y <c \cf x -> z = x)
       /\ ((\cf x <=c y) -> z = cnext x)))).
Proof.
move => icx y1 sch; rewrite /z.
have cy:= proj32 y1.
have x2:= (infinite_ge2 icx).
split => pa.
  apply: infinite_power1 => //.
  case: (finite_or_infinite cy) => // fy.
  have f2: finite_c (\2c ^c y). 
    by apply /NatP; apply: NS_pow; fprops; apply /NatP.
  case: (finite_not_infinite (cle_fin_fin f2 pa) icx).
have coi:=(cofinality_infinite_cardinal icx).
case: (finite_or_infinite cy) => // fy.
  split => h.
     have yN: natp y by apply  /NatP.
     rewrite (cpow_inf icx yN) //.
     by move/cge1P:y1 => [_ /nesym].
  case: (cleNgt h (clt_fin_inf fy coi)).
have yx:=(clt_leT (cantor (proj1 fy)) (proj1 pa)).
move: (ord_index_pr1 icx); set c := (ord_index x); move => [oc cv].
pose p1 x y :=( y <c \cf x -> x ^c y = x) /\
   (\cf x <=c y -> x ^c y = cnext x).
pose p2 x := forall y,  infinite_c y -> \2c ^c y <c x -> p1 x y.
pose p c := p2 (\aleph c).
rewrite -/(p1 _ _). suff: p2 x by move => h; apply: (h y). rewrite- cv.
apply: (least_ordinal2 (p:= p)) oc => d od lyd.
rewrite /p /p2.
clear cy pa fy z y1 yx y.
move => y icy yl1.
have yx:=(clt_leT (cantor (proj1 icy)) (proj1 yl1)).
case: (ordinal_limA od) => ln.
    by move: icy yx => / infinite_c_P2; rewrite ln aleph0E => h1 /(cleNgt h1).
  move: ln => [e oe es].
  move: (CS_aleph oe) => ie.
  have l1: \2c ^c y <=c \omega e.  
    by apply: cnext_pr4 => //; rewrite (cnextE oe) - es.
  have l2: (\aleph e) ^c y <=c \aleph d.
     case: (equal_or_not (\2c ^c y) (\aleph e)) => eq1.
        rewrite -eq1 - cpow_pow (csquare_inf icy);exact (proj1 yl1).
     have l3: \2c ^c y <c \omega e by split.
     have ed: e <o d by rewrite es; apply oltS.
     move:  (lyd _ ed _ icy l3) => [q4 q5].
     move: (CS_cofinality (proj1 ie)) => cc.
     case: (cleT_el cc (proj1 icy)) => cyx.
        rewrite (q5 cyx) (cnextE oe) -es; apply: cleR.
        by apply: CS_aleph.
     rewrite (q4 cyx); apply: aleph_le_lec;exact (proj1 ed).
  have l3: (\omega d) ^c y = \omega d.
     rewrite es (infinite_power2 oe (infinite_nz icy)).
     rewrite cprodC -es  (cprod_inf l2 (CIS_aleph od)) //.
     by apply: cpow_nz ; apply:  aleph_nz.
  move: (regular_initial_successor oe) => /regular_cardinalP [ _ h].
  by rewrite /p1 es h -es; split => // /(cltNge yx).
have aux: forall z, z <c (\omega d) -> z ^c y <c (\omega d).
   move => z z1.
   case: (finite_or_infinite (proj31_1 z1)) => fz.   
      case: (equal_or_not z \0c) => znz.
         by rewrite znz (cpow0x (infinite_nz icy)) - znz.
      case: (equal_or_not z \1c) => zno.
         by rewrite zno cpow1x - zno.
      move: (cge2 (proj31_1 z1) znz zno) => z2.
      by rewrite (infinite_power1_a z2 (cle_fin_inf fz icy) icy).
   move: (ord_index_pr1 fz); set e := (ord_index z); move=> [z2 z3].
   have ed: e <o d by apply: (aleph_ltc_lt z2 od); rewrite z3.
   case: (cleT_el (proj31_1 z1) (proj31_1 yl1)) => q1.
     by rewrite (infinite_power1 (infinite_ge2 fz) q1 icy).
   rewrite - z3 in q1.
   move: (lyd _ ed _ icy q1) => []; rewrite z3 => pa pb.
   move: (CS_cofinality (proj1 (proj1 fz))) => cc.
   case: (cleT_el cc (proj1 icy)) => cyx; last by rewrite (pa cyx).
   rewrite (pb cyx) - z3 (cnextE z2); apply: aleph_lt_ltc.
   move: ln => [_ _ ln1]; apply /oltP0.
   by split;fprops;apply: ln1; apply /oltP.
move: (CIS_aleph od) => icz.
move: (infinite_power9 icz icy) => [_ _ h]; move: (h  aux) => [h1 h2].
split => p3; first by apply: h1.
rewrite (h2 p3).
exact (sch _ icz (cle_ltT (cpow_Meqle card2_nz p3) yl1)).
Qed.

End Ordinals5.

Export  Ordinals5.
