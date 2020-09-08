(** * Theory of Sets : Miscellaneous results
  Copyright INRIA (2012-2013 2108) Marelle Team (Jose Grimm). 
*)



Set Warnings "-notation-overridden".
From mathcomp
Require Import ssreflect ssrbool eqtype ssrfun.
Set Warnings "-notation-overridden".

(* $Id: ssete11.v,v 1.8 2018/09/04 07:58:00 grimm Exp $ *)
Set Implicit Arguments.
Unset Strict Implicit.
Import Prenex Implicits.

Require Export sset14 ssete2 ssetq1.

Module CardinalSquare.
  
Lemma set_le_t a b: sub a b -> a <=s b.
Proof. move => ab; apply/set_leP; exists a; fprops. Qed.
  
Lemma set_leA a b: a <=s b -> b <=s a -> a \Eq b. 
Proof.
move => ha hb; exact: (CantorBernstein ha hb).
Qed.

Lemma set_leT: transitive_r set_le.
Proof.
move => y x z [f [fi sf tf]] [g [gi sg tg]].
exists (g \co f); saw; apply: (compose_fi fi gi);split; (try fct_tac); ue.
Qed.

Lemma set_le_i2 a b c: a <=s b -> b \Eq c -> a <=s c.
Proof.
move => [f [fb sf tf]] [g [[bg _] sg tg]].
exists (g \co f);saw; apply: compose_fi => //; split; (try fct_tac); ue.
Qed.

Lemma set_le_i1 a b c: a <=s b -> a \Eq c -> c <=s b.
Proof.
move => [f [fb sf tf]] /EqS [g [[bg _] sg tg]].
exists (f \co g);saw; apply: compose_fi => //; split; (try fct_tac); ue.
Qed.

Lemma set_lt_i2 a b c: a <s b -> b \Eq c -> a <s c.
Proof.
move => [ha hb] hc; split; first by  apply:(set_le_i2 ha hc).
dneg he; exact: (EqT he (EqS hc)).
Qed.

Lemma set_lt_i1 a b c: a <s b -> a \Eq c -> c <s b.
Proof.
move => [ha hb] hc; split; first by  apply:(set_le_i1 ha hc).
dneg he; exact: (EqT hc he).
Qed.

Lemma set_lt_leT a b c: a <s b -> b <=s c -> a <s c.
Proof.
move => [le1 ne] le2; move:(set_leT le1 le2) => le3.
split; [ exact | dneg eq1].
exact: (EqT eq1 (set_leA  (set_le_i1 le1 eq1) le2)).
Qed.

Lemma set_le_ltT a b c: a <=s b -> b <s c -> a <s c.
Proof.
move => le1 [le2 bc]; move:(set_leT le1 le2) => le3.
split; [ exact | move/EqS => eq1; case bc].
exact:(EqT (set_leA (set_le_i2 le2 eq1) le1) (EqS eq1)).
Qed.


Lemma order_le_total a b: worder a -> worder b -> a<=O b \/ b <=O a.
Proof. 
move => woa wob; move: (proj1 woa)(proj1 wob) => oa ob.
case: (isomorphism_worder_exists woa wob) => - [f [sf is1]].
  by left; apply:(order_le_alt oa ob); exists f.
by right; apply:(order_le_alt ob oa); exists f.
Qed.


Lemma set_le_total r A s B: worder_on r A -> worder_on s B ->
  A <s B \/ B <=s A.
Proof.
move =>[wor1 sr1][wor2 sr2].
have aux u v: u <=O v -> set_le (substrate u) (substrate v).
  move => [_ ov [f [x [xs [_ _ bp _]]]]].
  move: bp; rewrite (iorder_sr ov xs) => bp.
  by apply/set_leP; exists x => //; exists f.
case: (order_le_total wor1 wor2); move/aux; rewrite sr1 sr2;last by right.
move => lee.
case: (p_or_not_p (A \Eq B)) => h; last by left.
by right; apply/set_leP; exists A => //; apply: EqS.
Qed.

Lemma set_lt_notP a b:
   ~(a <s b) <-> (forall f, injection_prop f a b -> a \Eq b).
Proof.
split => H; last by case; case => f /H.
by move => f fp; ex_middle bad; case:H; split => //; exists f.
Qed. 

Lemma set_lt_not1 a b: a \Eq b ->  ~(a <s b).
Proof. by move => h; apply/set_lt_notP. Qed.

Lemma set_lt_Cantor M N:
  nonempty M ->
  (M <s N <->
  ( (exists N1, [/\ sub N1 N, nonempty N1 & N1 \Eq M]) 
    /\ ~ (exists M1, [/\ sub M1 M, nonempty M1 & M1 \Eq N]))).
Proof.
move => neM.
split.
  move =>[ h ne]; split.
     move/set_leP: h =>[M1 qa /EqS qb]; exists M1; split => //.
     apply/nonemptyP => me1.
     move:(EqS qb) => [g [bg sg tg]].
     case:neM => y; rewrite - sg => ysg.
     by move:(Vf_target (proj1(proj1 bg)) ysg); rewrite tg me1 => /in_set0.
  move => [M1 [qa qb /EqS qc]].
  have h2: N <=s M by apply/set_leP;exists M1.
  by case: ne; apply: set_leA.
move => [ [N1 [N1N _ /EqS p1]] p2].
split; first  by apply/set_leP; exists N1.
move => eq1; case: p2; exists M; split => //.
Qed.

  
Definition compare_wor r r' :=
  [/\ worder r, worder r' & 
    exists2 x, segmentp r' x & r \Is (induced_order r' x)].



Lemma compare_wor_prop r r': worder r -> worder r' ->
  (r <=O r'<-> compare_wor r r').
Proof.
move => wo1 wo2; move: (proj1 wo1) (proj1 wo2) => or1 or2.
split.
  move => [_ _ [f [x [sx fiso]]]].
  case: (isomorphism_worder_sub wo2 sx).
  set w := iso_seg_fun _ _ => wa wb.
  have  wc: (induced_order r' x) \Is (induced_order r' (target w)) by exists w.
  by split => //; exists (target w)  => //; apply:orderIT wc; exists f.
by move =>[_ _ [x [xs _] [f fi]]]; split => //; exists f,x.
Qed.

Lemma order_le_worA a b: worder a -> worder b -> a <=O b -> b <=O a ->
   a \Is b.
Proof.
move => woa wob.
move: (proj1 woa)(proj1 wob) => oa ob.
move/(compare_wor_prop woa wob) =>[_ _ [y ysb [f is1]]].
move/(compare_wor_prop wob woa) =>[_ _ [x xsa [g is2]]].
move:(proj1 ysb) (proj1 xsa) => syb sxa.
move: (iorder_osr ob syb) =>[or2 sr2].
move: (iorder_osr oa sxa) =>[or3 sr3].
move:is1 =>[_ _ [bf sf tf] fiso ]; rewrite sr2 in tf.
move:(is2) =>[_ _ [[[fg ig][_ sgg]] sg tg] giso ]; rewrite sr3 in tg.
have syg: sub y (source g) by ue.
have ff: function f by fct_tac.
move:(@fun_image_Starget1 g fg y); rewrite tg; set z:= Vfs g y => zx.
move:(sub_trans zx sxa) => zsc.
move:(iorder_osr oa zsc) =>[or4 sr4].
pose h  :=  (fun t => Vf g (Vf f t)).
have ax': lf_axiom h (substrate a) z.
  move => t tsx /=; apply/(Vf_image_P fg syg); exists (Vf f t) => //; Wtac.
have ax: lf_axiom h (substrate a) (substrate a) by move => t /ax' /zsc.
pose h1 := (Lf h (substrate a) (substrate a)).
have hinj: injection h1.
   apply: lf_injective => //; rewrite /h1.
   hnf; rewrite - sf; move => u v usr vsr ee.
   apply:(proj2(proj1 bf) _ _ usr vsr); apply: ig => //; apply: syg; Wtac.
have pd: order_morphism h1 a a.
  apply:(total_order_morphism (worder_total woa) oa hinj).
  - by rewrite /h1; aw.
  - by rewrite /h1; aw.
  - rewrite /h1; aw => u v usr vsr; rewrite !LfV// => leab.
    rewrite - sf in usr vsr.
    have fux: inc (Vf f u) (source g)  by apply: syg; Wtac.
    have fvx: inc (Vf f v) (source g)  by apply: syg; Wtac.
    move/(fiso u v usr vsr): leab => /iorder_gle1 ll.
    by move/(giso _ _ fux fvx) : ll => /iorder_gle1.
have pc: segmentp a (Imf h1).
  have fh: function h1 by fct_tac.
  have th: target h1 = (substrate a) by rewrite /h1; aw.
  have sh: source h1 = (substrate a) by rewrite /h1; aw.
  split; first by  rewrite - th; apply: Imf_Starget.
  move => u v /(Imf_P fh) [u1 u1h ->]; rewrite /h1.
  rewrite sh in u1h; rewrite LfV// => le1.
  have ha: inc (Vf f u1) (source g) by apply: syg; Wtac.
  have hb: inc (h u1) x by rewrite /h; Wtac.
  move:(proj2 xsa _ _ hb le1) => vx.
  have hc: inc v (target g) by ue.
  move: (sgg _ hc) =>[v1 v1sg v1v].
  have hd: inc (Vf f u1) (source g) by apply: syg; Wtac.
  have he: inc (Vf g v1) x by ue.
  have hf:  gle (induced_order a x) (Vf g v1) (Vf g (Vf f u1)).
    apply/iorder_gleP; split => //; ue.
  move/(giso v1 (Vf f u1) v1sg hd): hf => le3.
  have hi: inc (Vf f u1) y by Wtac.
  move:(proj2 ysb  (Vf f u1) v1 hi le3) => v1y.
  have hc': inc v1 (target f) by ue.
   move: ((proj2 (proj2 bf)) _ hc') =>[v2 v2sg v2v].
  apply/(Imf_P fh); exists v2; first by rewrite sh - sf. 
  have hk: inc v2 (substrate a) by ue.
  by rewrite /h1 LfV//; rewrite /h - v2v.
move:(unique_isomorphism_onto_segment woa pc pd) => hi.
move: is2.
have ->: x = substrate a.
  apply: extensionality => // t tb.
  move: (f_equal (Vf ^~t) hi); rewrite idV ///h1 LfV//  => <-.
  rewrite /h; Wtac; apply: syg; Wtac.
by rewrite (iorder_substrate oa) => ok; apply:orderIS; exists g.
Qed.



Definition worders E:= Zo (\Po (E\times E)) worder. 
Definition worders_eq E := graph_on order_isomorphic (worders E).
Definition worders_quo E:= quotient (worders_eq E).


Lemma wordersP E r :
  inc r (worders E) <-> exists2 F, sub F E & worder_on r F.
Proof.
split.
  move/Zo_P => [/setP_P ha hb]; exists (substrate r) => // x xsr.
  by case /setXp_P: (ha _ (proj42 (proj1 hb) x xsr)).
    move => [F FE [wor sr]]; apply: Zo_i => //; apply/setP_P.
move: (sub_graph_coarse_substrate (proj41 (proj1 wor))); rewrite sr => ss.
exact: (sub_trans ss (setX_Sll FE)).
Qed.

Lemma worders_wor E r : inc r (worders E) -> worder r.
Proof.  by move/wordersP =>[F _ /proj1]. Qed.

  
Lemma worders_eq_equivalence E:  equivalence (worders_eq E).
Proof.
apply: equivalence_from_rel; split; [ apply: orderIS |apply: orderIT].
Qed.


Lemma worders_eq_sr E: substrate (worders_eq E) = worders E.
Proof.
by apply: graph_on_sr => a /worders_wor /proj1 oa; apply: orderIR.
Qed.

Lemma worder_in_class_pr E x a: inc x (worders_quo E) -> inc a x ->
  x = class (worders_eq E) a.
Proof.
move: (worders_eq_equivalence E) => ee.
move => /funI_P[b bsr ->] /(class_P ee) rba.
by apply: (class_eq1 ee).
Qed.

Lemma worders_quo_isr E x a:
  inc x (worders_quo E) -> inc a x -> inc a (worders E).
Proof.
move => xq ax; move: (inc_in_setQ_sr (worders_eq_equivalence E) ax xq).
by rewrite worders_eq_sr.
Qed.
  
Lemma worders_quo_prop E x y a b:
  inc x (worders_quo E) -> inc y (worders_quo E) -> inc a x -> inc b y ->
  a \Is b -> x = y. 
Proof.
move: (worders_eq_equivalence E) => ee xq yq ax bx isab.
rewrite(worder_in_class_pr xq ax) (worder_in_class_pr yq bx).
move:(worders_quo_isr xq ax) (worders_quo_isr yq bx) => asr bsr.
by apply:(class_eq1 ee); apply/graph_on_P1.
Qed.

Definition  worders_qle E x y := 
  [/\ inc x (worders_quo E), inc y (worders_quo E) &
      exists a b, [/\ inc a x, inc b y & a <=O b]].

Lemma worders_eq_compat_le E a b c d:
  related (worders_eq E) a b -> related (worders_eq E) c d -> 
  (a <=O c <-> b <=O d).
Proof.
move => /graph_on_P0 [_ _ is1] /graph_on_P0 [_ _ is2].
exact: (order_le_compatible is1 is2).
Qed.

Lemma related_in_quo E x a b:
  inc x (worders_quo E) -> inc a x -> inc b x -> related (worders_eq E) a b.
Proof.
move:(worders_eq_equivalence E) => ee.
move/funI_P =>[z zr ->] /(class_P ee) r1 /(class_P ee) r2; equiv_tac.
Qed.
  
Lemma worders_qle_prop E x y: worders_qle E x y -> 
  forall a b, inc a x -> inc b y ->  a <=O b.
Proof.
move:(worders_eq_equivalence E) => ee.
move =>[ha hb [a1 [b1 [ a1x b1y cp1]]]] a b ax bx.
move: (related_in_quo ha ax a1x) (related_in_quo hb bx b1y) => qa qb.
by apply /(worders_eq_compat_le qa qb).
Qed.

Definition worders_order E := (graph_on (worders_qle E)(worders_quo E)).

Lemma worders_qle_propc E u v: 
  inc u (worders E) -> inc v (worders E) ->
  ( u <=O v <->
   gle (worders_order E) (class (worders_eq E) u)
     (class (worders_eq E) v)).
Proof.
move => usr vsr.
move:(worders_eq_equivalence E) => ee.
move:(usr)(vsr); rewrite - worders_eq_sr => usa vsa.
move:  (inc_itself_class ee usa) (inc_itself_class ee vsa) => ru rv.
split.
  move => h;  apply/graph_on_P1.
  move: (inc_class_setQ usa) (inc_class_setQ vsa) => cqu cqv.  
  by split => //; split => //; exists u, v.
move/graph_on_P1 =>[_ _ /worders_qle_prop cp]; exact: (cp _ _ ru rv).
Qed.

Lemma worders_qle_order E:
  order_on (worders_order E) (worders_quo E). 
Proof.
move:(worders_eq_equivalence E) => ee.
have refr: forall x, inc x (worders_quo E) -> worders_qle E x x.
  move => x xa; split => //;  move/funI_P: xa => [z ze ->].
  have zz: inc z (class (worders_eq E) z) by apply/(class_P ee); equiv_tac.
  exists z, z;split => //; apply: order_leR.
  by move: ze; rewrite worders_eq_sr => /wordersP [F _ /proj1/proj1].
move: (graph_on_sr refr).
set r := (graph_on (worders_qle E) (worders_quo E)) => sr.
split => //; apply: order_from_rel; split.
- move => y x z [xsr ysr [a [b [ax bx leab]]]] le2.
  move:(le2) => [_ /(setQ_ne ee) [c cz] _].
  move: (worders_qle_prop le2 bx cz) (proj32 le2)=> lebc zq. 
  split => //; exists a,c; split => //; apply: (order_leT leab lebc).
- move => x y [xsr ysr [a [b [ax bx leab]]]] le2.
  move: (worders_qle_prop le2 bx ax) => leba.
  move:(worders_quo_isr xsr ax)(worders_quo_isr ysr bx) => asr bsr.
  move: (worders_wor  asr) (worders_wor  bsr) => woa wob.
  exact:(worders_quo_prop xsr ysr ax bx (order_le_worA woa wob leab leba)).
- by move => x y [xq yq _]; split; apply: refr.
Qed.


Lemma worders_qle_total E: total_order (worders_order E).
Proof. 
move: (worders_qle_order E) =>[or sr].
split => //; rewrite sr => x y xq yq.
move:(worders_eq_equivalence E) => ee.
move:(setQ_ne ee xq) (setQ_ne ee yq) => [a iax] [b iby].
move:(worders_quo_isr xq iax) (worders_quo_isr yq iby)=> aw bw.
case: (order_le_total(worders_wor aw) (worders_wor bw)) => lab.
  by left; apply/graph_on_P1; split => //; split => //; exists a, b.
by right; apply/graph_on_P1; split => //; split => //; exists b, a.
Qed.


Lemma worders_qle_prop2 E X a:
  inc X (worders_quo E) -> inc a X ->
  a \Is (seg_order (worders_order E) X).
Proof.
move => Xq ax.
move:(worders_eq_equivalence E) => ee.
move: (worders_qle_order E) =>[wor sr].
set Z := segment (worders_order E)  X.
move:(worders_quo_isr Xq ax) => aw.
move:(worders_wor aw) => woa; move: (proj1 woa) => oa.
pose ios c := seg_order a c.
have hb x b: inc x Z -> inc b x -> exists2 c, inc c (substrate a) & b \Is ios c.
  move => /segmentP [/graph_on_P1 [xq _ lex] nexx] ibx.
  move:(worders_qle_prop lex ibx ax) => lba.
  move:(worders_quo_isr xq ibx) => bw.
  move:(worders_wor bw) => wob.
  move/(compare_wor_prop wob woa): lba =>[_ _ [y ysb [f is1]]].
  case:(well_ordered_segment woa ysb).
    move => ysa; move: is1; rewrite ysa (iorder_substrate (proj1 woa)) => is1.
    have ba: b \Is a by exists f.
    case: nexx; exact:(worders_quo_prop xq Xq ibx ax ba).
  by move => [c csr cv]; exists c => //; rewrite /ios/seg_order - cv; exists f.
have hc' c: inc c (substrate a)  -> inc (ios c) (worders E).
  move/wordersP: aw => [F sFE [_ sra]].
  move => csa; apply/wordersP.
  move: (@sub_segment a c) => s1.
  have ss:  sub (segment a c) E by apply:sub_trans sFE; rewrite - sra.
  by exists (segment a c) => //; apply:(seg_order_wosr).
have hc c: inc c (substrate a)  -> inc (ios c) (substrate (worders_eq E)).
  by rewrite worders_eq_sr; apply: hc'.
have hd c: inc c (substrate a) -> inc (class (worders_eq E) (ios c)) Z.
  move => cs; move: (hc _ cs) => ccs; apply/segmentP.
  move: (inc_itself_class ee ccs) => iic.
  split.
    have ra:=  (inc_class_setQ ccs).
    apply/graph_on_P1; split => //; split => //.
    move: (@sub_segment a c) => s1.
    exists (ios c), a; split => //.
    move:(seg_order_osr c oa) =>[or1 sr1].
    split => //;exists (identity (segment a c)), (segment a c); split => //.
    by rewrite -{1} sr1; apply: (identity_is or1).
  move => sv.
  move: ax; rewrite - sv; move=> /(class_P ee) /graph_on_P1 [ra _ /orderIS rc].
  apply: (segment_not_iso woa cs rc).
have he: sub Z (substrate (worders_order E)) by apply: sub_segment.
move:(iorder_osr wor he) =>[ orE srE].
pose f := Lf (fun c =>  (class (worders_eq E) (ios c))) (substrate a) Z. 
exists f; split => //.
  rewrite /f; hnf; aw; split  => //.
  apply: lf_bijective.
  - exact.
  - move => u v usa vsa scl. 
    move:(hc _ vsa) => ta.
    have: related  (worders_eq E) (ios u )(ios v).
      by apply/(class_P ee); rewrite scl; apply: (inc_itself_class ee).
    move/graph_on_P1 =>[tb tc td].
    exact:(iso_unique_segment woa usa vsa td).
  - move => y yZ.
    move: (he _ yZ); rewrite sr => yq;  move:(setQ_ne ee yq) => [b iby].
    move:(hb _ _ yZ iby) =>[c csr cc]; ex_tac.
    move:(hc' c csr) (worders_quo_isr yq iby)=> ics ibs.
    rewrite (worder_in_class_pr yq iby); apply: (class_eq1 ee).
    by apply/graph_on_P1.
rewrite /f; hnf; aw;trivial; move => u v usa vsa; rewrite !LfV//.
move:(hd _ usa)(hd _ vsa) => cus cvs.
move:(hc' _ usa)(hc' _ vsa) => iuE ivE.
apply: iff_trans (iff_sym (iorder_gle0P (worders_order E)  cus cvs)).
apply: iff_trans (worders_qle_propc iuE ivE).
have tb:  sub (segment a v) (substrate a) by apply: sub_segment.
move:(seg_order_osr u oa) =>[or1 tc].
move:(seg_order_osr v oa) =>[or2 td].
split => lr1.
  have ra: sub (segment a u) (segment a v) by apply: segment_monotone.
  have te:  sub (segment a u) (substrate a) by apply: sub_segment.
  split => //;exists (identity (segment a u)), (segment a u).
  rewrite -{2} tc td; split => //; rewrite (iorder_trans _ ra).
  by apply: (identity_is (proj1 (iorder_osr oa te))).
move/(compare_wor_prop (worders_wor iuE) (worders_wor ivE)): lr1.
move =>[ _ _ [x xs is1]].
move:(proj1 xs); rewrite td => sxg.
move: is1; rewrite /ios (iorder_trans _ sxg).
have [w le2 ->]: exists2 w, gle a w v & x = segment a w.
   case: (well_ordered_segment (worders_wor ivE) xs); rewrite td.
     by move ->; exists v => //; order_tac.
   move => [w /segmentP ll ->]; exists w. exact: (proj1 ll).
   by rewrite segment_induced.
by move /(iso_unique_segment woa usa (arg1_sr le2)) => ->.
Qed.

Lemma worders_qle_prop3 E: worder (worders_order E). 
Proof.
move: (worders_qle_order E) =>[or sr].
move:(worders_eq_equivalence E) => ee.
apply: (worder_prop_rev or) => T; rewrite sr => Tsr [X xT].
move:(Tsr _ xT) => Xq. move:(setQ_ne ee Xq) =>[a aX].
move:(worders_qle_prop2 Xq aX) => is1; set Z := segment (worders_order E) X.
pose  T0 := T\cap Z.
have zp x: inc x  (worders_quo E) -> inc x Z \/ gle (worders_order E) X x.
  move => xq; move:(xq) => xq1; rewrite - sr in Xq xq.
  case: (total_order_pr2 (worders_qle_total E) xq Xq) => lt; last by right.
  by left; apply/segmentP.
case: (emptyset_dichot T0) => te.
  ex_tac => b bt; case: (zp _ ((Tsr _ bt))) => // bZ. 
  by empty_tac1 b; apply: setI2_i.
move: (orderIS is1) =>[f fiso].
have aux: sub Z (substrate (worders_order E)) by apply: sub_segment.
move:fiso =>[oa ob]; rewrite (iorder_sr or aux); move => [bf sf tf] ffi.
have sub1: sub T0 (source f) by rewrite sf; move => t /setI2_P[].
have ff := (proj1 (proj1 bf)).
move:(Vf_image_P ff sub1) => vfsP.
have sub2: sub (Vfs f T0) (substrate a). 
  by rewrite - tf; apply: fun_image_Starget1.
have nee: nonempty (Vfs f T0) by apply:(nonempty_image ff te sub1). 
move:(worders_quo_isr Xq aX) => aw.
move:(worders_wor aw) => woa.
move:(worder_prop woa sub2 nee) =>[b /vfsP [Y /setI2_P [yY yZ] uv] bl]; ex_tac.
move => C cT.
move/Zo_P: (yZ)=> [two [mt1 nxy]].
case: (zp  _ ((Tsr _ cT))) => cZ; last by  order_tac.
move: (setI2_i cT cZ) => ct0.
have /bl: inc (Vf f C) (Vfs f T0) by  apply/vfsP; ex_tac.
rewrite - sf in yZ cZ.
by rewrite uv; move/(ffi Y C yZ cZ) => /iorder_gleP; case.
Qed.

Lemma worder_transportation r E G g: worder_on r E -> bijection_prop g E G ->
  exists2 s, worder_on s G & r \Is s.
Proof.
move =>[wor sr] [bg sf tg].
have sr1: (substrate r) = source g by ue. 
move:(order_transportation bg (conj (proj1 wor) sr1)); set s := Vfs _ _ => oig.
have is1: r \Is s by exists g.
move: (worder_invariance is1 wor) => wo1.
exists s => //; split => //; rewrite - tg.
by move: (oig) =>[_ _ [_ _ sr2] _].  
Qed.


Lemma worders_qle_prop4 E: (worders_quo E) <=s E -> False.
Proof.
move => [f [injf sf tf]].
move:(Imf_Starget (proj1 injf)); rewrite tf; set G :=  Imf f => sGE.
move:(restriction_to_image_fb injf); set g := restriction_to_image f => bg.
have bgp:  bijection_prop g (worders_quo E) G.
  by split => //; rewrite /g/restriction_to_image/restriction2; aw.
have srQ := (proj2 (worders_qle_order E)).
move: (conj (worders_qle_prop3 E) srQ) => H.
move:(worder_transportation H bgp) => [r wor is1].
have rw: inc r (worders E) by apply/wordersP; exists G => //; split => //; ue.
move:(worders_eq_equivalence E) => ee.
have xsrr: inc r (substrate (worders_eq E)) by rewrite worders_eq_sr.
set X := class (worders_eq E)r.
have xq: inc X (worders_quo E) by apply: inc_class_setQ.
have rX: inc r X by apply: inc_itself_class.
have Xsr2: inc X (substrate (worders_order E)) by ue.
move: (worders_qle_prop2 xq rX) => is2.
case: (segment_not_iso  (worders_qle_prop3 E) Xsr2); exact: (orderIT is1 is2).
Qed.

Lemma wor_from_injection E Q r f: worder_on r Q ->
  injection_prop f E Q ->
  (exists r, worder_on r E). 
Proof.
move => [wor sr] [[ff injf] sf tf].
move: (proj1 wor) => or.
pose cp x y := gle r (Vf f x) (Vf f y).
have rre a: inc a E -> cp a a.
  move => ae; rewrite /cp; order_tac;  rewrite sr; Wtac.
set s := graph_on cp E.
have srE: substrate s = E by rewrite graph_on_sr.
have os: order s. 
  rewrite/s/cp;apply: order_from_rel1.
  - move => y x z /= ha hb; order_tac.
  - move => x y xE yE l1 l2.
    have: (Vf f x) = (Vf f y)  by order_tac.
    apply: injf; ue.
  - done.
exists s; split => //; apply:(worder_prop_rev os) => x xE xnE.
set A := fun_image x (Vf f).
have neA: nonempty A by apply: funI_setne.
have sas: sub A (substrate r).
  by rewrite sr =>t /funI_P [j jx ->]; Wtac; rewrite sf - srE; apply: xE.
move: (worder_prop wor sas neA) =>[a aA al].
move/funI_P: aA => [u ue uv]; ex_tac => b bx.
move:(xE _ ue)(xE _ bx) ; rewrite srE => qa qb.
apply /graph_on_P1; split => //. rewrite /cp; rewrite - uv; apply: al.
apply/funI_P; ex_tac.
Qed.
  
Lemma worders_qle_prop5 E:
  (exists f, injection_prop f E (worders_quo E)) <->
  (exists r, worder_on r E). 
Proof.
move: (worders_qle_order E) =>[orQ srQ].
split.
  move=>[f ff];apply:(wor_from_injection (conj (worders_qle_prop3 E)srQ) ff).
move => [r wor]; move: (proj2 wor) => sr.
have rw: inc r (worders E) by  apply/wordersP; exists E => //.
move:(worders_eq_equivalence E) => ee.
have xsrr: inc r (substrate (worders_eq E)) by rewrite worders_eq_sr.
set X := class (worders_eq E)r.
have xq: inc X (worders_quo E) by apply: inc_class_setQ.
have rX: inc r X by apply: inc_itself_class.
move: (worders_qle_prop2 xq rX) => [f [ _ _  is2 _]].
move:(is2) =>[[[ff ii ] _] sf tf].
exists (Lf (Vf f) E  (worders_quo E)); saw.
have sz1: sub (target f) (worders_quo E).
  by rewrite tf (proj2 (seg_order_osr X orQ)) - srQ; apply: sub_segment.
rewrite - {1} sr - sf; apply: lf_injective.
   move => t te; apply: sz1; Wtac.
by move => u v iE vE; apply: ii.
Qed.


Lemma worders_qle_prop6 E
  (Z := Zo (worders_quo E) (fun z => exists2 y, inc y z & substrate y \Eq E))
  (X := the_least (induced_order (worders_order E) Z))
  (Y := seg_order (worders_order E) X):
  (exists f, injection_prop f E (worders_quo E)) ->
  worder Y /\ substrate Y \Eq E.
Proof.
move /worders_qle_prop5 => [r wor]; move: (proj2 wor) => sr.
have rw: inc r (worders E) by  apply/wordersP; exists E => //.
move:(worders_eq_equivalence E) => ee.
move: (worders_qle_order E) =>[orQ srQ].
have xsrr: inc r (substrate (worders_eq E)) by rewrite worders_eq_sr.
set C := class (worders_eq E)  r.
have cq: inc C (worders_quo E) by apply: inc_class_setQ.
have CZ: inc C Z.
  apply: (Zo_i cq); exists r; first by apply:inc_itself_class.
  rewrite (proj2 wor); apply: EqR.
have nez: nonempty Z by ex_tac.
have zs: sub Z (substrate (worders_order E)). rewrite srQ; apply: Zo_S.
move:(iorder_osr orQ zs) =>[or1 sr1].
move: (worders_qle_prop3 E) => woQ.
split; first by apply: (seg_order_wor _ woQ).
move: (proj1(the_least_pr or1 (proj2 woQ _ zs nez))).
rewrite sr1; move => /Zo_P [Xq [a aX etc]].
move: (worders_qle_prop2 Xq aX) =>[f [_ _ bf _]].
have eq1: (substrate a) \Eq substrate Y by exists f.
exact: (EqT (EqS eq1) etc).
Qed.

Definition aleph_of a b := 
  [/\ worder b, ~ ((substrate b) <s a) &  ~ (a <s (substrate b))].

Lemma aleph_of_prop1 a b: worder_on b a -> aleph_of a b.
Proof.
move =>[qa qb]; split => //; rewrite qb; apply:set_lt_not1; fprops.
Qed.

Lemma aleph_of_prop2 a b: aleph_of a b ->
  (a <=s (substrate b) \/ (substrate b) <=s a) ->
  exists2 r, worder_on r a & b \Is r.
Proof.
move => [ha / set_lt_notP hb / set_lt_notP hc] hd.
have /EqS [f fp]: a \Eq (substrate b).
  case: hd; move => [f fp]; [ apply: (hc f fp) | apply: EqS; apply:(hb f fp)].
exact:(worder_transportation (conj ha (erefl (substrate b))) fp).
Qed.


Definition one_aleph_of E :=
  let r :=  worders_order E in
  let Z := Zo (worders_quo E) (fun z => ~  (segment r z) <s E) in
  let X0 := the_least (induced_order r Z) in
  let X1 := Yo (nonempty Z)  (segment r X0) (worders_quo E) in
  (induced_order r X1).

Lemma  one_aleph_of_prop  E:
  aleph_of E (one_aleph_of E).
Proof.
rewrite /one_aleph_of.
set r := worders_order E.
set Z := Zo _ _; set X0 := the_least _; set X1 := Yo _ _ _.
have pa:  ~ (worders_quo E) <s E.
  apply/set_lt_notP => f fp. 
  have /worders_qle_prop4//: (worders_quo E) <=s E by exists f.
move:(worders_qle_order E) => [orQ srQ].
have wor := (worders_qle_prop3 E).
have ZQ: sub Z (substrate (worders_order E)) by rewrite srQ; apply: Zo_S.
pose s X := [/\ segmentp r X, ~ X <s E & 
   forall t, inc t X -> (segment r t) <s E].
have ra: nonempty Z -> s (segment r X0).
  move => ze.
  move: (iorder_osr orQ ZQ) =>[oZ sZ].
  move:(the_least_pr oZ (proj2 wor Z ZQ ze)); rewrite -/X0.
  case; rewrite sZ; move =>/Zo_P[xQ hx1] etc.
  have ss: segmentp r (segment r X0) by  apply: segment_segment.
  split => // t/segmentP ltr.
  case: (inc_or_not t Z) => itz.
    move:(etc _ itz) => /iorder_gleP [_ _Ø] le; order_tac.
  by ex_middle bad; case: itz; apply: Zo_i;first  by rewrite - srQ; order_tac.
have rb: ~ (nonempty Z) -> s (worders_quo E).
  split => //; first by rewrite - srQ;  apply: substrate_segment.
  move => t tsr; ex_middle bad.
  case: (inc_or_not t Z) => itz; first by case :H; ex_tac.
  by case: itz; apply: (Zo_i tsr).
have [qa qb qc]: s X1 by rewrite /X1; Ytac foo; fprops.
move:(proj1 qa) => sr2; move: (induced_wor wor sr2) => wo2.
split => //; rewrite (iorder_sr orQ sr2) => //; case.
move => [f [ff sf tf]].
move:(Eq_src_range ff); rewrite sf => eq2.
case; apply: (EqT eq2).
have eq1 := (iorder_sr orQ sr2).
move:(Imf_Starget (proj1 ff)); rewrite tf => ss1.
move:(ss1); rewrite  - {1} eq1 => ss2.
case: (isomorphism_worder_sub wo2 ss2)O.
set w := iso_seg_fun _ _ => ws.
move:(proj1 ws); rewrite eq1 => ss3.
rewrite (iorder_trans _ ss1) (iorder_trans _ ss3) => is1.
have eqxi : Imf f \Eq (target w).
  move: is1 => [_ _ kp _]; move: kp.
  rewrite (iorder_sr orQ (sub_trans ss1 sr2)).
  rewrite (iorder_sr orQ (sub_trans ss3 sr2))=> is1.
  exact: (equipotent_bp is1).
case: (well_ordered_segment (induced_wor wor sr2) ws).
  by rewrite eq1 => <-.
move => [x].
rewrite (iorder_sr orQ sr2) => x1X.
rewrite (segment_induced_a qa x1X) => vw.
case: (proj2 (qc _ x1X)); rewrite - vw; exact: (EqS(EqT eq2 eqxi)).
Qed.

Definition Sfinite x := x <s Nat.
Definition Sinfinite x := ~ Sfinite x.
Definition Saleph x := Sinfinite x /\ exists r, worder_on r x.


Lemma Sinfinite_inv x y: Sinfinite x -> x \Eq y -> Sinfinite y.
Proof. 
move => ha hb hc; case: ha; exact :(set_lt_i1 hc (EqS hb)).
Qed.


Lemma Saleph_inv A M: Saleph A ->  A \Eq M ->  Saleph M.
Proof.
move =>[ha [r wor]] cam; split; first exact:(Sinfinite_inv ha cam).
move: cam =>[f fp]; move: (worder_transportation wor fp) =>[s wos _]. 
by exists s.
Qed.

Lemma Saleph_Nat: Saleph Nat.
Proof.
move: Nat_order_wor => wo2.
by split; [ move =>[_ ]; case; apply: EqR | exists Nat_order ].
Qed.  

Lemma Sinfinite_mon a b: Sinfinite a -> a <=s b -> Sinfinite b. 
Proof. move => ha hb hc; case: ha. apply: (set_le_ltT  hb hc). Qed.
 
Lemma Saleph_mon a b: Sinfinite a -> a <=s b -> Saleph b ->  Saleph a.
Proof.
move => ia [f fab] [ha [r wor]] ; split => //.
exact:(wor_from_injection wor fab).
Qed.

Lemma set_compare_to_finite  E n: natp n -> E <s  n \/ n <=s E.
Proof.
move: n; apply: Nat_induction.
  by right; apply: set_le_t => t /in_set0.
move => n nN.
move: (succ_of_nat nN) => r1.
have ha: n <=s csucc n.
  by apply:set_le_t; rewrite r1 => t tx; apply: setU1_r.
case; first by move => hb;move:(set_lt_leT  hb ha) => hc; left.
move => /set_leP [X sXE exn].
move/NatP: (nN)=> [/ordinal_irreflexive nn fn].
case: (equal_or_not X E) => xe.
  rewrite - xe; left; split; first by  move: (set_le_i1 ha exn).
  rewrite r1; move => h;case fn; exact:(EqT  exn h).
move: (setC_ne (conj sXE xe)) => [y /setC_P[yE ynX] ]; right.
apply /set_leP; exists (X +s1 y); first by apply: setU1_sub.
by rewrite r1; apply/(succ_inf_aux_p1).
Qed.

Lemma proposition_S E (A := substrate (one_aleph_of E)):
   Sinfinite E -> [/\ Saleph A, ~ E <s A & ~  A <s E].
Proof.
move => einf.
case: (one_aleph_of_prop E);rewrite -/A => sa sb sc; split => //.
split; last by exists (one_aleph_of E).
move => Ad.
have  [n nN ean] : exists2 n, natp n & A \Eq n.
  move:Nat_order_wor => [wo2 sr2].
  case:(isomorphism_worder2 sa wo2).
  -  move => [f [_ _]]; rewrite -/A sr2 =>  fp _. 
     by case: Ad => _; case; exists f.
  - rewrite -/A; move =>[x xA [f [_ _]]].
    move: (@sub_segment  (one_aleph_of E) x); set u := segment _ _ => s1.
    rewrite (iorder_sr (proj1 sa) s1) sr2 => bf _.
    have h: Nat <=s A by apply/set_leP; exists u => //; apply: EqS; exists f.
    case:(set_lt_leT Ad h) => _; case; apply: EqR.
  - move => [n ]; rewrite sr2 => nN. 
    rewrite /seg_order (segment_Nat_order1 nN).
    have ha: sub n (substrate Nat_order) by  rewrite sr2 => t / (NS_inc_nat nN).
    move =>[f [_ _ ]]; rewrite (iorder_sr (proj1 wo2) ha) => fp _.
    by exists n => //; apply: EqS; exists f. 
case: (set_compare_to_finite E nN) => lt.
  by move:(set_lt_i2 lt (EqS ean)).
move: (set_le_i1 lt (EqS ean)) => lt1; case: sb.
by split => // aa; move:(set_lt_i1 Ad aa).
Qed.


Lemma Eq_F_doubleE F a b A B : inc a F -> inc b F -> a <> b ->
   sub A F -> sub F B ->
   F \Eq (coarse F) -> A \Eq (B -s F) -> 
   F \Eq B.
Proof.
move => aF bR anb sAF sFB eFF /EqS [g [[[fg gi] _] sg tg]].
apply:CantorBernstein; first by apply: set_le_t.
have ra: B <=s B \times B. 
  exists (Lf (J a) B (B \times B)).
  saw; apply: lf_injective; first by move => t tB; apply:setXp_i; fprops.
  by move => u v _ _ /=/pr2_def.
have rb:  B <=s F \times F. 
  exists (Lf( fun z => (Yo (inc z F) (J a z) (J b (Vf g z)))) B (F\times F)).
  saw; apply: lf_injective.
    move => x xb /=; Ytac h; apply: setXp_i => //; apply: sAF; Wtac.
    by rewrite sg; apply/setC_P.
  move => u v uB vB /=; Ytac ha; Ytac hb => /pr12_def [hc hd]//.
  - by case: anb.
  - by move: hd;apply: gi; rewrite sg; apply/setC_P. 
have rc:=(set_le_i2 rb (EqS eFF)).
have rd: coarse B <=s coarse F.
  move: rc =>[h [[fh hi] sh tf]].
  exists (Lf (fun z => (J (Vf h (P z)) (Vf h (Q z)))) (coarse B) (coarse F)).
  saw; apply: lf_injective.
    move => z /setX_P[pz za ab]; apply:setXp_i; Wtac.
  move => u v /setX_P [pu ua ub]/setX_P[pv va vb] /pr12_def [esa sb].
  apply:(pair_exten pu pv); apply: hi; ue.
exact:(set_leT ra (set_le_i2 rd (EqS eFF))).
Qed.



Definition  bij_double_F2_fun F G a b f g := 
  let fi := inverse_fun f  in let gi := inverse_fun g in
  let H := (G\times F \cup G\times G) \cup F \times G in
  let alpha := fun x y => J a (Vf fi (J x (Vf gi y))) in
  let beta := ( fun y => (Yo (inc y F) (J a y) (J b (Vf gi y)))) in
  let gamma := fun x y => J b (Vf fi (J (Vf gi x) (Vf fi (beta y)))) in
  let f2:= fun p =>  Vf g (Vf fi 
   (Yo (inc (P p) F) (alpha (P p) (Q p)) (gamma (P p) (Q p)))) in
  let f3 := (cantor_bernstein_bij G H (Lf (J a) G H) (Lf f2 H G)) in
  let f4 := (fun x => Yo (inc x F) (Vf f x) (Vf f3 x)) in
  Lf f4  (F \cup G) (coarse (F\cup G)).

Lemma bij_double_F2 F G a b f g : inc a F -> inc b F -> a <> b ->
  disjoint F G ->
  bijection_prop f F (coarse F) ->
  bijection_prop g F G ->
  let h :=  bij_double_F2_fun F G a b f g in 
   bijection_prop h (F \cup G) (coarse (F\cup G)) /\ extends h f.
Proof.
move => aF bF anb di fp gp.
move:(inverse_bij_bp fp)(inverse_bij_bp gp).
set gi := inverse_fun g; set fi := inverse_fun f.
move =>[[[ffi ifi] sjfi] sfi tfi] [[[fgi igi] sjgi] sgi tgi].
move:(proj31 gp) => bg;move: gp =>[[[fg ig] [_ sjg]] sg tg].
move: fp =>[[[ff iff] [_ sjf]] sf tf].
set FG := F \cup G.
pose H := (G\times F \cup G\times G) \cup F \times G.
have Hv: H = G \times FG \cup F\times G. 
  by rewrite /H - set2_UXr.
have di1: disjoint (G \times FG) (F \times G).
  apply:disjoint_pr => u /setX_P[_ pg _] /setX_P[_ pf _];empty_tac1 (P u).
have du2: disjoint (coarse F) H.
  clear di1.
  rewrite Hv;apply:disjoint_pr =>  x /setX_P[_ x1 X2]; case/setU2_P.
    move=> /setX_P[_ y1 y2]; empty_tac1 (P x).
  move=> /setX_P[_ y1 y2]; empty_tac1 (Q x).
set alpha := fun x y => J a (Vf fi (J x (Vf gi y))).
have alpha_p0 x y: inc x F -> inc y G -> inc (J x (Vf gi y)) (source fi).
  move => xE yF;  rewrite sfi; apply: setXp_i => //; Wtac.
have alpha_p1 x y: inc x F -> inc y G -> inc (alpha x y) (coarse F).
  move => xE yF; apply: (setXp_i aF); Wtac. 
have alpha_p2 x y x' y': inc x F -> inc y G -> inc x' F -> inc y' G ->
    (alpha x y)  = (alpha x' y') -> x = x' /\ y = y'. 
  move => qa qb qc qd /pr2_def e1.
  move:(pr12_def (ifi _ _ (alpha_p0 _ _ qa qb)(alpha_p0 _ _ qc qd) e1)).
  move=> [qe qf]; split => //; apply: igi; ue.
set beta := ( fun y => (Yo (inc y F) (J a y) (J b (Vf gi y)))).
have beta_p1 y: inc y FG -> inc (beta y) (coarse F). 
  rewrite /beta; move => yH; Ytac w; apply:setXp_i => //; Wtac.
  by rewrite sgi;case/setU2_P:yH.
have beta_p2 y y':  inc y FG -> inc y' FG -> beta y = beta y' -> y = y'. 
  rewrite/beta;move=> yH yH'; Ytac w; Ytac wb; move => /pr12_def [qa qb].
  - exact.
  - by case anb.  
  - by case anb.  
  - by move: qb;apply: igi;rewrite sgi;case/setU2_P:yH=> //; case/setU2_P:yH'.
set gamma := fun x y => J b (Vf fi (J (Vf gi x) (Vf fi (beta y)))).
have gamma_p0 x y: inc x G -> inc y FG ->
   inc (J (Vf gi x) (Vf fi (beta y))) (source fi).
  move => xa yb; rewrite sfi; apply: setXp_i; Wtac.
  by rewrite sfi; apply beta_p1.
have gamma_p1 x y: inc x G -> inc y FG -> inc (gamma x y) (coarse F).
  move => xa yb; apply: (setXp_i bF); Wtac. 
have gamma_p2 x y x' y': inc x G -> inc y FG -> inc x' G -> inc y' FG ->
   gamma x y =  gamma x' y' -> x = x' /\ y = y'. 
  move => qa qb qc qd /pr2_def e1.
  move:(pr12_def (ifi _ _ (gamma_p0 _ _ qa qb) (gamma_p0 _ _ qc qd) e1)). 
  move=> [qz qf]; split; [ apply: igi; ue |  apply: beta_p2 => //].
  apply: ifi => //;ue.
set f2:= fun p =>  Vf g (Vf fi 
   (Yo (inc (P p) F) (alpha (P p) (Q p)) (gamma (P p) (Q p)))).
set f3 := (cantor_bernstein_bij G H (Lf (J a) G H) (Lf f2 H G)).
have Hw x: inc x G -> ~ inc x F.
  by  move => qa qb; case: (@in_set0 x); rewrite - di; apply/setI2_P.
have delta_p0 p: inc p H -> inc (Yo (inc (P p) F)
              (alpha (P p) (Q p)) (gamma (P p) (Q p))) (source fi).
  rewrite Hv sfi ;case/setU2_P => /setX_P[pp pa pb].
    by rewrite (Y_false (Hw _ pa)); apply: gamma_p1.
   by Ytac0;apply: alpha_p1.
have delta_p1 p: inc p H -> inc (f2 p) G.
  move => pg; rewrite /f2;Wtac; rewrite sg; Wtac. 
  by rewrite tfi; apply: delta_p0.
have delta_p2 p q: inc p H -> inc q H ->  f2 p = f2 q -> p = q.
  move => pH qH ea.
  move:(delta_p0 p pH) (delta_p0 q qH) => sa sb.
  move:(Vf_target ffi sa) (Vf_target ffi sb); rewrite tfi - {2 4} sg => sc sd.
  move:(ifi _ _ sa sb (ig _ _ sc sd ea)).
  rewrite Hv in  pH qH.
  case/setU2_P:pH => /setX_P[pp pa pb];case/setU2_P:qH => /setX_P[pq pc pd].
  + rewrite (Y_false (Hw _ pa)) (Y_false (Hw _ pc)) => eb.
    by move: (gamma_p2 _ _ _ _ pa pb pc pd eb) =>[ua ub]; apply:pair_exten.
  + by rewrite (Y_false (Hw _ pa)); Ytac0;move/pr1_def => ab; case: anb.
  + by rewrite (Y_false (Hw _ pc)); Ytac0;move/pr1_def => ab; case: anb.
  + Ytac0; Ytac0 => eb; move: (alpha_p2 _ _ _ _ pa pb pc pd eb)  =>[ua ub]. 
    by apply:pair_exten.
have cb1: injection_prop (Lf f2 H G) H G.
  by saw;apply: lf_injective.
have cb2: injection_prop (Lf (J a) G H) G H.
  saw; apply: lf_injective.
    by rewrite Hv; move => x xG; apply: setU2_2; apply: setXp_i.
  by move => u v _ _ /pr2_def.
move: (CantorBernstein_eff cb2 cb1); rewrite -/f3.
move => [[[ff3 if3] [_ sjf3]] sf3 tf3].  
have ra: sub F FG by  apply: subsetU2l.
have uFH: coarse F \cup H = coarse FG.
  by rewrite Hv (setU2_C (G \times FG)) setU2_A /coarse - set2_UXr - set2_UXl.
have rc: sub H (coarse FG) by rewrite - uFH; apply: subsetU2r.
pose aux := (fun x => Yo (inc x F) (Vf f x) (Vf f3 x)).
have rd t: inc t FG -> ~inc t F -> inc t G by case/setU2_P.
have Hu t: inc t G -> inc (Vf f3 t) H by move => itg; Wtac.
have ax: lf_axiom  aux FG (coarse FG).
  rewrite/aux; move => x xFG /=; Ytac xf; first by  apply: (setX_Sll ra); Wtac.
  by apply:rc; apply: Hu; apply: rd.
set K := Lf aux FG (coarse FG).
have Kp: bijection_prop K FG (coarse FG).
  rewrite /K/aux; saw; apply: lf_bijective.
  - exact.
  - move => u v uFG vFG; Ytac uf; Ytac vf.
    + apply: iff; ue.
    + move:(rd _ vFG vf) => sa sv.
      by empty_tac1 (Vf f u); [ Wtac | rewrite sv; apply:Hu ].
    + move:(rd _ uFG uf) => sa sv.
      by empty_tac1 (Vf f v); [ Wtac | rewrite - sv; apply:Hu ].
    + by apply: if3; rewrite sf3; apply: rd.
  - move => y yv;case: (inc_or_not y (coarse F)).
      rewrite -tf; move/sjf; rewrite sf; move =>[x xf ->]. 
      by exists x; [ apply: ra | Ytac0 ].
    move => yc; move: yv; rewrite - uFH; case/setU2_P => //; rewrite -tf3=>yH.
    move:(sjf3 _ yH); rewrite sf3; move =>[x xs ->].
    exists x; first by apply:setU2_2.
    Ytac xx; [by clear di1 du2; empty_tac1 x | done].
move: (Kp) => [bk sk tk]; have fK: function K by fct_tac.
have stk: sub (target f) (target K). 
   by rewrite tf tk; apply: setX_Sll; apply: ra.
have ssk: sub (source f) (source K) by  rewrite sf sk.    
split; split => //. 
apply/(sub_functionP ff fK); split => //.
move => t; rewrite sf /K/aux => tF; move:(ra _ tF) => tFG.
by rewrite LfV//; Ytac0.
Qed.

Lemma Saleph_square E: Saleph E -> E \Eq  (E \times E).
Proof. 
move => [einf [r [wor sr]]]; move:(proj1 wor) => or.
have H a b : a \Is b -> (substrate a) \Eq (substrate b).
  by move =>[f [_ _ fp _]]; exists f.
move:Nat_order_wor => [wor2 sr2].
move:(EqS equipotent_N2_N) => resa. 
have Hu x y: x \Eq (coarse x) -> x \Eq y -> y \Eq (coarse y).
  move => ha hb; exact: (EqT (EqS hb)  (EqT ha (Eq_mul_inv hb hb))).
case: (p_or_not_p (Nat \Eq E)) => ne.
   move: ne =>[f fp]; have ne: Nat \Eq E by exists f.
   exact: (Hu _ _ resa ne).
case:(isomorphism_worder2 wor2 wor).
    by move /H; rewrite sr sr2.
  move =>[x];rewrite sr2; move:(@sub_segment Nat_order x) => qa qb.
  move/H; rewrite (iorder_sr (proj1 wor2) qa); rewrite sr => /EqS hh.
  case:einf; split; last by move => rn1; case: ne; apply: EqS.
  apply/set_leP; exists (segment Nat_order x) => //; ue.
move =>[x0]; rewrite sr; move:(@sub_segment r x0).
set S0 := (segment r x0) =>S0E xE is1.
move: is1 =>[f1 [_ _ fp _]]; move: fp;rewrite (iorder_sr or S0E) sr2 => fp.
pose a0 := Vf (inverse_fun f1) C0.
pose a1 := Vf (inverse_fun f1) C1.
move:(fp) => [qa qb qc].
have ha: inc C0 (target f1) by rewrite qc; apply: NS0.
have hb: inc C1 (target f1) by rewrite qc; apply: NS1.
move:(inverse_Vis qa ha) (inverse_Vis qa hb); rewrite qb -/a1 -/a0 => a0S0 a1S1.
have aneb: a0 <> a1.
  move => /(f_equal (Vf f1)).
  rewrite  (inverse_V qa ha) (inverse_V qa hb); fprops.
clear qa qb qc ha hb.
have qa:  S0 \Eq Nat by exists f1.
move:(Hu _ _ resa (EqS qa)) =>[f0 f0p].
rewrite sr in S0E.
clear fp qa  ne resa einf.
pose Gi g := forall y, singl_val (fun x => inc (J x y) g).
pose T0 := \Po (E \times (E\times E)).
pose pra G := [/\ fgraph G, Gi G, range G = coarse (domain G),
    segmentp r (domain G) & sub S0 (domain G)] .
pose prb f:= [/\ bijection_prop f (source f) (coarse (source f)),
   segmentp r (source f) &  sub S0 (source f)]. 
have ra f: prb f -> pra (graph f).
  move =>[[[fi fs ] sf tf] ssf xp]; hnf.
  have gig: Gi (graph f) by move => y; apply: (injective_pr3 fi).
  move:(proj1 fi) => ff; move: (function_fgraph ff) => fgf.
  rewrite (domain_fg ff).
  move: (surjective_pr0 fs); rewrite (ImfE ff) => ->; rewrite -tf; done.
have ra' f: sub (source f) E -> prb f -> inc (graph f) T0.
  move => hu [[bf sf tf] hb hc]; apply/setP_P.
  have ff := (proj1 (proj1 bf)).
  move: (sub_graph_setX (proj1 (function_fgraph ff))).
  rewrite (domain_fg ff) => hyp t /hyp /setX_P[pt r1 r2].
  apply/setX_P; split => //; first by apply: hu.
  move: r2; rewrite - (ImfE ff) => r3; move: (Imf_Starget ff  r3); rewrite tf.
  by move => /setX_P [pu r4 r5]; apply/setX_P; split => //; apply: hu.
pose Fg g := (triple (domain g) (range g) g).
have rb g: pra g -> prb (Fg g).
  rewrite/Fg; move =>[qa qb qc qd qe]; hnf; saw.
  rewrite /bijection_prop; aw; rewrite - qc; split => //.
  have ff:  function (triple (domain g) (range g) g).
    apply: function_pr => //.
  split; first by apply: (injective_pr_bis ff); aw.
  by apply: (surjective_pr1 ff); rewrite (ImfE ff); aw.
have rb' g: inc g T0 ->  sub (source (Fg g)) E.
  by move => /setP_P h; rewrite /Fg; aw => t /funI_P [z /h /setX_P [_ zz _] ->].
pose T1 := Zo T0 pra.
have neT: inc (graph f0) T1.
   move: (f0p) =>[bf sf tf].
   have h: (prb f0) by rewrite /prb sf; split => //; apply:segment_segment.
   by apply: Zo_i; [ apply: (ra' f0 _ h); ue | apply: ra].
pose tot X := total_order (induced_order (sub_order T1) X).
have rc: forall X, sub X T1 -> nonempty X -> tot X ->
    inc (union X) T1 /\ forall y, inc y X -> sub y (union X). 
  move => X ha hb hc; split; last first.
    move => y yX t  yx; union_tac.
  apply: Zo_i.
    by apply/setP_P => t /setU_P [u uy /ha /Zo_S /setP_P h]; apply: h.
  have to u v: inc u X -> inc v X -> sub u v \/ sub v u.  
    move:(sub_osr T1) =>[sa sb].
    have sc: sub X (substrate (sub_order T1)) by rewrite sb.
    move => ux vx; move: (proj2 hc u v); rewrite (iorder_sr sa sc) => sd.
    move:(sd ux vx); case;  move=> /iorder_gle1 /sub_gleP; case; auto.
  move: (domain_setU X) => dx.
  have res4:  segmentp r (domain (union X)).
    rewrite dx; apply: setU_segment =>t/funI_P [z zX ->].
    by move:(ha _ zX) => /Zo_hi [].
  have res5:  sub S0 (domain (union X)).
    move: hb => [x xX];move:(ha _ xX) => /Zo_hi [_ _ _ _] ss. 
    apply: (sub_trans ss).
    by rewrite dx => t ts;apply/setU_P; exists (domain x) => //; apply: funI_i.
  have res3: range (union X) = coarse (domain (union X)).
    rewrite dx range_setU; set_extens t.
      move => /setU_P[y ry /funI_P[z zx zv]].
      move:(ha _  zx) => /Zo_hi[_ _ rx _ _].
      have: sub (domain z) (union (fun_image X domain)).
        by move => s sd; apply/setU_P; exists (domain z) => //; apply: funI_i.
      by move/ setX_Sll; apply; rewrite -rx - zv.
    move => /setX_P [pt t1 t2].
    move: t1 => /setU_P[x1 x1v /funI_P [y1 y1X y1v]].
    move: t2 => /setU_P[x2 x2v /funI_P [y2 y2X y2v]].
    case: (to _ _ y1X y2X) => ss.
      apply/setU_P; exists (range y2); last by apply: funI_i.
      move:(ha _  y2X) => /Zo_hi [_ _ -> _ _]; apply/setX_P. 
      split; [ exact | apply:(domain_S ss); ue | ue ].
    apply/setU_P; exists (range y1); last by apply: funI_i.
    move:(ha _  y1X) => /Zo_hi [_ _ -> _ _]; apply/setX_P. 
    split; [ exact | ue | apply:(domain_S ss); ue ].
  have res1:  fgraph (union X).
    split. 
      by move => t/setU_P [y ty /ha/Zo_hi [[hu _] _ _ _ _]]; apply: hu.
    move => u v /setU_P [x tx xX] /setU_P [y ty yX] sp. 
    move: (xX) (yX) => /ha/Zo_hi [[_ hx] _ _ _ _] /ha/Zo_hi [[_ hy] _ _ _ _].
    case: (to _ _ xX yX) => ss.
     by apply: hy => //; apply: ss.
    by apply: hx => //; apply: ss.
  have res2: Gi (union X).
     move => z u v  /setU_P [x tx xX] /setU_P [y ty yX]. 
     move: (xX) (yX) => /ha/Zo_hi [_ hx _ _ _] /ha/Zo_hi [_ hy _ _ _].
     case: (to _ _ xX yX) => ss.
       by apply: (hy z) => //; apply: ss.
     by apply: (hx z) => //; apply: ss.
  done. 
move:(sub_osr T1) =>[orT1 srT1].
pose max x :=  Yo (x = emptyset) (graph f0) (union x).
have max_prop s:
     sub s (substrate (sub_order T1)) ->
     worder (induced_order (sub_order T1) s) ->
     upper_bound (sub_order T1) s (max s).
  rewrite srT1 => st wot1; rewrite /max; Ytac se.
    by split; [  rewrite srT1| rewrite se => y /in_set0].
  move /nonemptyP: se => se.
  move: (rc s st se (worder_total wot1)) =>[qa qb]; split; first by ue.
  by move => y ys; move: (st _ ys)(qb _ ys) => qc qd; apply/sub_gleP. 
case: (all_exists_dichot2 (fun t => (domain t) \Eq E) T1); last first.
   move =>[f /Zo_P [qa qb]].
   move:(rb _ qb) =>[]; rewrite /Fg; aw; set g := triple _ _ _ => bg  _ _ ee.
   have eq1: (domain f) \Eq (coarse (domain f)) by exists g.
   apply:(Hu _ _ eq1 ee).
move => T1_small.
pose iorc x := (induced_order r (E -s x)).
pose isof x := (iso_seg_fun (induced_order r (domain x))  (iorc (domain x))).
pose na x := bij_double_F2_fun (domain x) (target (isof x)) a0 a1 (Fg x)
   (isof x).
suff rd x: inc x T1 ->  inc (graph (na x)) T1 /\ ssub x (graph (na x)).
  have next_prop x: 
     inc x (substrate (sub_order T1)) -> glt (sub_order T1) x (graph (na x)).
    rewrite srT1 => xt1; move: (rd _ xt1) =>[qa [qb qc]].
    by split=> //;apply/sub_gleP.
  by case:(Zorn_aux_eff orT1 max_prop next_prop).
move => xT1.
move:(T1_small x xT1) => noti.
move/Zo_P: (xT1) =>[/setP_P sX xp].
move: (rb _ xp) =>[bp _ _];move: bp; rewrite  {2 3} /Fg; aw => bp.
move: xp => [_ _ _ sdx ss ].
have sdE: sub (domain x) (substrate r).
  by move => t /funI_P [z /sX /setX_P[_ ok _] -> ]; rewrite sr.
have iaf: inc a0 (domain x) by apply: ss.
have ibf: inc a1 (domain x) by apply: ss.
move: (induced_wor wor sdE) => wo1.
have scE: sub (E -s (domain x)) (substrate r).
  by move => y /setC_P; rewrite sr; case.
move: (induced_wor wor scE); rewrite -/(iorc _) => wo2.
set rF := (induced_order r (domain x)).
set rG := (iorc (domain x)).
move: (iorder_sr or sdE) (iorder_sr or scE) => sru srv.
case: (isomorphism_worder_exists_v1 wo1 wo2); last first.
  set  F := inverse_fun _.
  move =>[[qa _] [_ _ /inverse_bij_bp qb _]]. 
  rewrite sru in qa.
  have st:= (sub_trans qa sdE).
  have eq2:  (domain x) \Eq (coarse (domain x)) by exists (Fg x).
  move: qb; rewrite srv (iorder_trans _ qa) (iorder_sr or st) => eea.
  have eqe: (target F) \Eq (substrate r -s domain x).
    by rewrite sr; exists (inverse_fun F).
  by case: noti; move:(Eq_F_doubleE iaf ibf aneb qa sdE eq2 eqe); rewrite sr.
set f := iso_seg_fun _ _.
move => [qa  [_ _ qb _]].
move:(proj1 qa); rewrite srv => qc.
have qd: sub (target f) (substrate r).
   by rewrite sr; move => t / qc /setC_P; case.
move: qb; rewrite sru /iorc (iorder_trans _ qc) (iorder_sr or qd) => qb.
have di: disjoint (domain x) (target f).
  by apply:disjoint_pr => t tdx / qc /setC_P [].
move:(bij_double_F2 iaf ibf aneb di bp qb).
simpl; rewrite  -/(na x).
move => [hp1 hp2].
have sh: source (na x) =  (domain x \cup target f) by case: hp1.
have s0H: sub S0 (source (na x)).
   by rewrite sh;move => y / ss yd; apply:setU2_1.
have sdhE:  sub (source (na x)) E by rewrite sh - sr; apply: setU2_12S.
have ssh:  segmentp r (source (na x)).
  split; [ by rewrite sr | rewrite sh ].
  move => a b /setU2_P ai lba; case: ai => ai. 
    apply: setU2_1;exact:(proj2 sdx _ _ ai lba).
  case: (inc_or_not b (domain x)) => bdx;  first by apply: setU2_1.
  have ad:  inc a (E -s domain x).
    by apply/setC_P;split;[rewrite - sr; order_tac | move=> ad; empty_tac1 a].
  have snd: inc b (E -s domain x).
     apply/setC_P; split => //; rewrite - sr; order_tac.
  have le1: gle (iorc (domain x)) b a by apply/iorder_gleP.
  apply: setU2_2; exact: (proj2 qa a b ai le1).
rewrite - sh in hp1. 
have prbh: prb (na x) by [].
have ht1: inc (graph (na x)) T1 by apply: Zo_i; [ apply: ra' | apply: ra].
split => //.
split; first by move:(proj43 hp2); rewrite /Fg; aw.
have fh: function (na x) by move: hp1 => [[[]]].
move => sg; move:(f_equal domain sg); rewrite domain_fg // sh => bad.
move: qb => [[[ff _] _]sf tf].
have asf: inc a0 (source f) by rewrite sf.
move:(Vf_target ff asf) => utf.
have udx: (inc (Vf f a0) (domain x)) by rewrite bad; apply: setU2_2.
empty_tac1 (Vf f a0).
Qed.

Lemma Sfinite2: C2 <s Nat.
Proof.
split.
  apply: set_le_t =>t /set2_P; case => ->;  [apply:NS0 | apply: NS1].
move =>[f [[[ff fi] [_ fs]] sf tf]].
set a := (Vf f C0); set b := Vf f C1.
have aN: natp a by rewrite /a /natp; Wtac; rewrite sf;apply: set2_1.
have bN: natp b by  rewrite /b /natp; Wtac; rewrite sf;apply: set2_2.
move:(Nmax_p1 aN bN) =>[cN /(cltSleP cN)/proj2 ha /(cltSleP cN) /proj2 hb].
move:(NS_succ cN); rewrite /natp - tf => /fs [c csf /esym].
by move:csf; rewrite  sf; case/set2_P => ->. 
Qed.

Lemma set_lt_2inf x: Sinfinite x ->  C2 <s x. 
Proof.
move: Sfinite2 => ha xi.
case: (p_or_not_p (x\Eq  Nat)) => en.
  exact:(set_lt_i2 ha (EqS en)).
split; last by move => hb; move:(set_lt_i1 ha hb).
case:(set_compare_to_finite x NS2) => // - [lx2 _]; case:xi.
split => //; apply:(set_leT lx2 (proj1 ha)).
Qed.
  
Lemma set_le_2P x : C2 <=s x ->
  exists a b, [/\ inc a x, inc b x & a <> b].
Proof.
move =>[f [[ff fi] sf <-]].
move:(set2_1 C0 C1)(set2_2 C0 C1); rewrite -/C2 - sf => sa sb.
exists (Vf f C0), (Vf f C1); split; try Wtac; move/(fi _ _ sa sb); fprops.
Qed.

Lemma Sinfinite_ne x: Sinfinite x -> nonempty x.
Proof.
move=> /set_lt_2inf/proj1/set_le_2P [a [_ [ai _ _]]]; ex_tac.
Qed.  

Lemma set_le_ab_sab2 A B: 
  A \times B <=s  coarse (dsum A B).
Proof.
pose f x y := (J (J x C0) (J y C1)).  
exists (Lf (fun z => f (P z) (Q z)) (A\times B) (coarse ((dsum A B)))).
saw; apply: lf_injective.
  move => t /setX_P [ pt qa qb].
  apply:setXp_i; [ by apply: candu2_pra | by apply: candu2_prb].
move => u v /setX_P [ pu qa qb] /setX_P [ pv qc qd].
by move=> /pr12_def [ /pr1_def ha /pr1_def hb]; apply: pair_exten.
Qed.

Lemma set_le_ab_sab A B: C2 <=s A -> C2 <=s B ->
  dsum A B <=s A\times B. 
Proof.
move => /set_le_2P [a0 [a1 [ha hb ne1]]].
move => /set_le_2P [b0 [b1 [hc hd ne2]]]. 
pose f z := Yo (Q z = C0) (J (P z) b0)
               (Yo (P z = b0) (J a1 b1) (J a0 (P z))).
exists(Lf f (dsum A B)  (A \times B)); saw; apply: lf_injective.
  rewrite /f; move => x /candu2P [px]; case; move =>[ra rb].
    by Ytac0; apply:setXp_i.
  by rewrite rb; Ytac0; Ytac w;apply:setXp_i.
move => u v /candu2P [pu pp] /candu2P [pv pp']; rewrite -{2} pu -{2} pv /f; 
case:pp; case pp';move => [sa ->] [sb ->]; Ytac0; Ytac0.
- by move => /pr1_def ->.
- by Ytac w; [ move/pr2_def | move/pr2_def=> t; case: w ].
- by Ytac w; [ move/pr2_def=> t; case: ne2 | move/pr2_def ].
- Ytac w1; Ytac w2.
  - by rewrite w1 w2.
  - by move/pr1_def => t; case: ne1.
  - by move/pr1_def.
  - by move/pr2_def ->.
Qed.

Lemma Eq_sum_mono1 A B: A <=s (dsum A B).
Proof.
exists (Lf (fun z => J z C0) A (dsum A B)).
saw;apply: lf_injective; first apply:candu2_pra.
by move => u v _ _ /pr1_def.
Qed.

Lemma Eq_sum_mono1_bis A B: B <=s (dsum A B).
Proof. exact:(set_le_i2 (Eq_sum_mono1 B A) (Eq_sumC B A)). Qed.

Lemma Eq_sum_mono2 A B C: A <=s B -> (dsum A C) <=s (dsum B C).
Proof.
move =>[f [[ff fi] sf tb]].
exists (Lf (fun p=> Yo (Q p = C0) (J (Vf f (P p)) C0) p) (dsum A C) (dsum B C)).
saw; apply:lf_injective.
  move => t /candu2P [pt]; case => - [qa qb];rewrite qb; Ytac0.
    apply: candu2_pra; Wtac.
  by rewrite -pt qb;apply: candu2_prb. 
move: C0_ne_C1 C1_ne_C0 => pa pb.
move => u v  /candu2P [pu ha] /candu2P [pv hb];case: ha; case: hb.
- rewrite -{6} pv - {6} pu ;move =>[sa ->] [sb ->]; Ytac0; Ytac0 => /pr1_def h.
  congr J; apply: fi => //;ue.
- rewrite -{5} pv; move =>[sa ->] [sb ->]. 
  by Ytac0; Ytac0 => /pr2_def h; case:pa. 
- rewrite -{5} pu; move =>[sa ->] [sb ->]. 
  by Ytac0; Ytac0 => /pr2_def h; case:pa. 
- by move =>[sa ->] [sb ->] ; Ytac0; Ytac0.
Qed.

Lemma Eq_mul_mon1 a b:  nonempty b -> a <=s a \times b.
Proof.
move =>[x xb]; exists (Lf (fun z => J z x) a (a\times b)); saw.
apply: lf_injective; first by move => z za; apply: setXp_i.
by move => u v _ _ /pr1_def.
Qed.


Lemma Eq_mul_mon2 a b c: b <=s c -> a \times b <=s  a \times c.
Proof.
move =>  [f [[ff fi] sf tf]].
exists (Lf (fun t => J (P t) (Vf f (Q t))) (a \times b) (a \times c));saw.
apply: lf_injective.
  move => t /setX_P [_ ha ]; rewrite  - sf => /(Vf_target ff); rewrite tf => h.
  by apply setXp_i.
move => u v /setX_P [pu ha hb] /setX_P [pv cb hd] /pr12_def [eq1 eq2]. 
apply: (pair_exten pu pv eq1); apply: fi; try ue. 
Qed.


Lemma Saleph_double x: Saleph x -> x \Eq (x \times C2).
Proof.
move => h; move:(Saleph_square h) => a2.
apply: CantorBernstein.
   have nec2: nonempty C2 by exists C0; apply: set2_1.
   exact: (Eq_mul_mon1 x nec2).
exact: (set_le_i2 (Eq_mul_mon2 x (proj1 (set_lt_2inf (proj1 h)))) (EqS a2)).
Qed.

Lemma Saleph_double' x: Saleph x -> x \Eq (C2 \times x).
Proof.
move =>/Saleph_double => h; exact: (EqT h (Eq_setX2_S x C2)).
Qed.


Lemma Eq_add_square A  B:
  (coarse (dsum A B)) \Eq
    dsum (dsum (coarse A) (coarse B)) ((A \times B)\times C2).
Proof.
pose f x y fx fy :=
  Yo (fx = C0) (Yo (fy = C0) (J (J (J x y) C0) C0)  (J (J (J x y) C0) C1))
               (Yo (fy = C0) (J (J (J y x) C1) C1)  (J (J (J x y) C1) C0)).
pose g := fun z => f (P (P z)) (P (Q z)) (Q (P z)) (Q (Q z)).
exists (Lf g (coarse (dsum A B))
   (dsum (dsum (coarse A) (coarse B)) ((A \times B) \times C2))).
move:(set2_1 C0 C1) (set2_2 C0 C1); rewrite -/C2 => i1 i2.
move: C0_ne_C1 C1_ne_C0 => C01 C10.
saw; apply: lf_bijective.
- move => t /setX_P [pt /candu2P [ha hb] /candu2P [hc hd]].
  rewrite /g/f; case:hb =>- [hb ->];case:hd =>- [hd ->]; Ytac0; Ytac0.
  + by apply: candu2_pra; apply: candu2_pra; apply: setXp_i.
  + by Ytac0;apply: candu2_prb;apply: setXp_i => //;apply: setXp_i.
  + by apply: candu2_prb;apply: setXp_i => //;apply: setXp_i.
  + by apply: candu2_pra; apply: candu2_prb; apply: setXp_i.
+ rewrite/g/f;  move => u v /setX_P [pt /candu2P [ha hb] /candu2P [hc hd]].
  move => /setX_P [pt' /candu2P [ha' hb'] /candu2P [hc' hd']] h.
  rewrite - pt - pt' - ha -hc -ha' -hc'; move: h.
  case:hb =>- [hb ->];case:hd =>- [hd ->]; Ytac0; Ytac0;
     case:hb' =>- [hb' ->];case:hd' =>- [hd' ->]; Ytac0; Ytac0.
  + by move/pr1_def /pr1_def/pr12_def => [-> ->].
  + by Ytac0; move /pr2_def =>h; case: C01.
  + by move /pr2_def =>h; case: C01.
  + by move /pr1_def /pr2_def =>h; case: C01.
  + by Ytac0; move/pr2_def => h ;case: C10.
  + by Ytac0;Ytac0;move/pr1_def /pr1_def/pr12_def => [-> ->].
  + by Ytac0; move /pr1_def /pr2_def =>h; case: C01.
  + by Ytac0; move/pr2_def => h ;case: C10.
  + by move/pr2_def => h ;case: C10.
  + by Ytac0;move/pr1_def /pr2_def => h ;case: C10.
  + by move/pr1_def /pr1_def/pr12_def => [-> ->].
  + by move/pr2_def => h ;case: C10.
  + by move/pr1_def /pr2_def => h ;case: C10.
  + by  Ytac0; move /pr2_def =>h; case: C01.
  + by  move /pr2_def =>h; case: C01.
  + by move/pr1_def /pr1_def/pr12_def => [-> ->].
move => y /candu2P [px]; case => - [qa qb].
  case/candu2P: qa => ppy; case => - [ha hb].
    move/setX_P: ha =>[c1 c2 c3].
    exists (J (J  (P (P (P y))) C0) (J (Q (P (P y))) C0)).
      by apply:setXp_i; apply:candu2_pra.
    by rewrite /g; aw; rewrite /f; Ytac0;Ytac0;rewrite c1 - {1} hb - qb ppy px.
  move/setX_P: ha =>[c1 c2 c3].
  exists (J (J  (P (P (P y))) C1) (J (Q (P (P y))) C1)).
    by apply:setXp_i; apply:candu2_prb.
  by rewrite /g; aw; rewrite /f; Ytac0; Ytac0;rewrite c1 - {1} hb - qb ppy px.
move:qa=> /setX_P [py /setX_P [c1 c2 c3] /set2_P]; case => qq.
  exists (J (J  (P (P (P y))) C0) (J (Q (P (P y))) C1)).
    by apply:setXp_i; [ apply:candu2_pra | apply:candu2_prb]. 
  rewrite /g; aw; rewrite /f; Ytac0; Ytac0;Ytac0. 
  by rewrite c1 - qq py - qb px.
exists (J (J  (Q (P (P y))) C1) (J (P (P (P y))) C0)).
    by apply:setXp_i; [ apply:candu2_prb | apply:candu2_pra]. 
  rewrite /g; aw; rewrite /f; Ytac0; Ytac0.
  by rewrite -{2} qb c1 - qq py. 
Qed.


Lemma Eq_square_mul a b: 
  coarse (a \times b) \Eq (coarse a) \times (coarse b).
Proof.
move:(Eq_mulA (a \times b) a b) => ra.
move: (Eq_mul_inv (EqS (Eq_mulA a b a)) (EqR b)) => rb.
move:(EqT (Eq_mul_inv (EqR a) (Eq_setX2_S b a)) (Eq_mulA a a b)) => rc.
move: (EqS (Eq_mulA (coarse a) b b)) => rd.
exact:(EqT (EqT (EqT ra rb) (Eq_mul_inv rc (EqR b))) rd).
Qed.

Lemma Eq_muldl a b c: 
  (dsum b c) \times a \Eq dsum (b \times a) (c \times a).
Proof.
apply:(EqT (EqT (Eq_setX2_S (dsum b c) a) (Eq_muldr a b c))).
exact:(Eq_sum_inv (Eq_setX2_S a b) (Eq_setX2_S a c)).
Qed.


Lemma Eq_squareE x : (coarse x) \Eq (functions C2 x).
Proof.
apply:EqS.
exists (Lf (fun z => (J (Vf z C0) (Vf z C1)))  (functions C2 x) (coarse x)).
move:(set2_1 C0 C1)(set2_2 C0 C1); rewrite -/C2 => i1 i2.
saw; apply: lf_bijective.
+ move => f/functionsP[ff sf tf]; apply:setXp_i; Wtac.
+ move => f g/functionsP[ff sf tf] /functionsP[fg sg tg].
  move /pr12_def =>[va vb]; apply: function_exten => //; try ue.
  by rewrite sf => y /set2_P; case => ->.
+ move => y /setX_P[py y1 y2].
  have ax: lf_axiom (variant C0 (P y) (Q y)) C2 x.
  by move => t xtp;  try_lvariant xtp.
  exists (Lf (variant C0 (P y) (Q y)) C2 x).
    by apply /functionsP; saw; apply: lf_function.
  by rewrite ! LfV//; aw; rewrite py.
Qed.

Lemma Eq_pow_mon1 a b: nonempty b  -> a <=s functions b a.
Proof.
move => [w wb].
exists (Lf (fun t => Lf (fun _ => t) b a) a (functions b a)).
saw; apply: lf_injective.
  by move => x xa; apply /functionsP; saw;apply:lf_function => t.
move => u v ua va /(f_equal (Vf ^~ w)); rewrite !LfV// => s.
Qed.


(* wwwwwwwwwwwwwwwwwwwwwwwww *)


Definition proposition_Z:=
  forall x, Sinfinite x -> Saleph x.

Lemma propositionZ_zermelo: proposition_Z ->
  forall x, exists r, worder_on r x.
Proof.
move => h x; case: (p_or_not_p (Sfinite x)); last by case/h.
move:Nat_order_wor => wor [[f fab] _].
exact:(wor_from_injection wor fab).
Qed.



Lemma tarski_lemma1 M A: Saleph A -> M \times A \Eq dsum M A ->
  A <=s M \/ M <=s A.
Proof.
move => [_ [r [wor osr]]] /EqS [f [bf sf tf]].
have ff: function f by fct_tac.
pose M1 := fun_image M (fun z => Vf f (J z C0)).
pose A1 := fun_image A (fun z => Vf f (J z C1)).
have qm t: inc t M -> inc (Vf f (J t C0)) M1.
  move => tm; apply/funI_P; ex_tac.
have qa t: inc t A -> inc (Vf f (J t C1)) A1.
  move => tm; apply/funI_P; ex_tac.
have ha: sub M1 (M \times A).
  by move => t /funI_P [z zM ->]; Wtac; rewrite sf; apply: candu2_pra.
have hb: sub A1 (M \times A).
  by move => t /funI_P [z zM ->]; Wtac; rewrite sf; apply: candu2_prb.
have hc: M \times A = M1 \cup A1.
  set_extens t; last by case/setU2_P; fprops.
  rewrite - tf => /(proj2(proj2 bf)) [x xsf ->].
  move: xsf; rewrite sf => /candu2P [pp]; case.
    by move =>[sa sb]; apply:setU2_1; apply/funI_P; ex_tac; rewrite - sb pp.
  by move =>[sa sb]; apply:setU2_2; apply/funI_P; ex_tac; rewrite - sb pp.
have hd: disjoint M1 A1.
  apply/set0_P => t /setI2_P [/funI_P [a al ->] /funI_P [b bM bb]].
  have asf : inc  (J a C0) (source f) by rewrite sf; apply: candu2_pra.
  have bsf : inc  (J b C1) (source f) by rewrite sf; apply: candu2_prb.
  move: (pr2_def (proj2 (proj1 bf) _ _ asf bsf bb)); fprops.
pose fM := Lf (fun z => Vf f (J z C0)) M M1.
pose fA := Lf (fun z => Vf f (J z C1)) A A1.
have bfM: bijection_prop fM M M1. 
  rewrite /fM;saw; apply: lf_bijective.
  - done.
  - move => u v uM vM sfv.
    have usf : inc  (J u C0) (source f) by rewrite sf; apply: candu2_pra.
    have vsf : inc  (J v C0) (source f) by rewrite sf; apply: candu2_pra.
    exact: (pr1_def (proj2 (proj1 bf) _ _ usf vsf sfv)).
  - by move =>y /funI_P.
have bfA: bijection_prop fA A A1. 
  rewrite /fA;saw; apply: lf_bijective.
  - done.
  - move => u v uM vM sfv.
    have usf : inc  (J u C1) (source f) by rewrite sf; apply: candu2_prb.
    have vsf : inc  (J v C1) (source f) by rewrite sf; apply: candu2_prb.
    exact: (pr1_def (proj2 (proj1 bf) _ _ usf vsf sfv)).
  - by move =>y /funI_P.
have he: M  \Eq  M1 by exists fM.
have hf: A  \Eq  A1 by exists fA.
pose p m := forall a, inc a A -> inc (J m a) M1.
case: (all_exists_dichot2 p  M); last first.
  move => [m mp pm].
  have le1: A <=s M1. 
    exists  (Lf (fun z => J m z) A M1). 
    by saw; apply: lf_injective => // u v _ _ /pr2_def. 
  left; exact: (set_le_i2 le1 (EqS he)).
move => hp.
have hp1: forall m, inc m M -> exists2 a, inc a A & inc (J m a) A1.
  move => m mM; move:(hp _ mM) => pmm.
  case:(all_exists_dichot1 (fun a => inc (J m a) M1) A) => // - [a aA av].
  move: (setXp_i mM aA); rewrite hc; case/setU2_P => // ok; ex_tac.
pose phi m := the_least (induced_order r (Zo A (fun a => inc (J m a) A1))).
have hg m: inc m M -> inc (J m (phi m)) A1. 
  move => mM; rewrite /phi; set Z := Zo _ _.
  have sz: sub Z (substrate r) by rewrite osr; apply: Zo_S.
  have nez: nonempty Z.
    by move:(hp1 _ mM) => [a aa ab]; exists a; apply: Zo_i.
  move:(iorder_osr (proj1 wor) sz) =>[oZ sZ].
  move: (proj1 (the_least_pr oZ (proj2 wor _ sz nez))).
  by rewrite sZ => /Zo_hi.
have le1: M <=s A1.
  exists (Lf (fun m => (J m (phi m))) M A1).
  by saw; apply: lf_injective => //  u v _ _ /pr1_def.
right; exact: (set_le_i2 le1 (EqS hf)).
Qed.


Lemma Tarski_th1_aux M A: Sinfinite M ->  Saleph A ->
   ~ M <s A -> ~ A <s M  -> M \times A \Eq dsum M A  -> Saleph M.
Proof.
move => im pa pb pc res.
case: (p_or_not_p (A \Eq M)) => eac.
  apply: (Saleph_inv  pa eac).
by case: (tarski_lemma1 pa res) => h; [case: pc | case: pb; split => // /EqS].
Qed.


Lemma Tarski_th1:
  (forall x y, Sinfinite x -> Sinfinite y -> x \times y \Eq dsum x y) -> 
  proposition_Z.
Proof.
move => Hyp c ci; move: (proposition_S ci) => [pa pb pc].
exact: (Tarski_th1_aux ci pa pb pc (Hyp _ _ ci (proj1 pa))).
Qed.



Lemma Tarski_th2:
  (forall x, Sinfinite x -> coarse  x \Eq x) ->
  proposition_Z.
Proof.
move => H; apply: Tarski_th1 => x y xi yi.
have zi := (H _ (Sinfinite_mon xi (Eq_sum_mono1 x y))).
apply:set_leA; first exact:(set_le_i2 (set_le_ab_sab2 x y) zi).
move:(proj1 (set_lt_2inf xi)) (proj1 (set_lt_2inf yi)) => xs ys.
by apply:set_le_ab_sab. 
Qed.

Lemma Tarski_th3:
  (forall x y, Sinfinite x -> Sinfinite y ->
     (coarse x) \Eq (coarse y) -> x \Eq y) ->
  proposition_Z.
Proof.
move => hyp m mi.
have nse: nonempty Nat by exists \0c; apply: NS0.    
move:(Eq_pow_mon1 m nse).
set n := functions _ _ => lmn.
apply: (Saleph_mon mi lmn).
have ni:= (Sinfinite_mon mi lmn).
move: (proposition_S ni); set a := substrate _;move => [pa pb pc].
pose p := dsum n a; pose q := n \times  a.
have ai :=  (proj1 pa).
have nea:= (Sinfinite_ne ai).
have lenp: n <=s p by apply: Eq_sum_mono1.
have lenq: n <=s q by apply:(Eq_mul_mon1 _ nea). 
move: (Sinfinite_mon ni lenp) (Sinfinite_mon ni lenq) => pi qi.
apply:(Tarski_th1_aux ni pa pb pc); apply: EqS; apply:(hyp p q pi qi).
have nn: n \Eq (coarse n).
  move:(Eq_pow_inv (EqR m) (Saleph_double Saleph_Nat))(Eq_powpow m Nat C2).
  move => sa sb.
  exact:(EqT (EqT sa sb) (EqS (Eq_squareE n))).
move: (Saleph_square pa)(Saleph_double pa) => sa da.
have sq: coarse q \Eq q.
  exact :(EqT (Eq_square_mul n a) (Eq_mul_inv (EqS nn) (EqS sa))). 
have dq: q \times C2 \Eq q.
  exact: (EqT (EqS  (Eq_mulA n a C2)) (Eq_mul_inv (EqR n) (EqS da))).
have lpq: p <=s q.
  move:(proj1 (set_lt_2inf ni)) (proj1 (set_lt_2inf ai)) => nl al.
  exact:(set_le_ab_sab nl al).
have eq1: dsum p q \Eq q.
  apply: set_leA; last exact: (set_le_i2 (Eq_sum_mono1 q p) (Eq_sumC q p)).
  move: (Eq_sum_mono2 q lpq); rewrite dsum_same => h.
  exact: (set_le_i2 h  dq).
move:(EqT (Eq_add_square n a) (EqS (Eq_sum_inv (Eq_sum_inv nn sa) (EqS dq)))).
move=> h; exact:(EqT (EqT h eq1) (EqS sq)).
Qed.


Lemma Tarski_th4:
  (forall x y z t, 
    Sinfinite x -> Sinfinite y -> Sinfinite z -> Sinfinite t ->
    x <s y -> z <s t -> (dsum x z) <s  (dsum y t)) -> 
  proposition_Z.
Proof.
move => hyp m mi.
have nse: nonempty Nat by exists \0c; apply: NS0.
move: (Eq_mul_mon1 m nse); set n := product _ _  => lmn.
have ni:= (Sinfinite_mon mi lmn).
move: (proposition_S ni); set a := substrate _;move => [pa pb pc].
apply: (Saleph_mon mi lmn).
case:(p_or_not_p (a \Eq n)) => ean; first exact: (Saleph_inv pa ean).
move: (Eq_sum_mono1 n a) (Eq_sum_mono1_bis n a) => le1 le2.
case: (p_or_not_p (n \Eq (dsum n a))) => eq1.
  case: pc; split => //; exact:(set_le_i2 le2 (EqS eq1)).
case: (p_or_not_p (a \Eq (dsum n a))) => eq2.
  by case: pb; split; [ exact:(set_le_i2 le1 (EqS eq2)) | move/EqS].
have pi:= (Sinfinite_mon ni le1).
case:(proj2 (hyp _ _ _ _  ni pi (proj1 pa) pi  (conj le1 eq1) (conj le2 eq2))).
move:(Saleph_double pa) => aa.
move:(EqT (Eq_mul_inv (EqR m) (Saleph_double Saleph_Nat)) (Eq_mulA m Nat C2)).
rewrite -/ n => nn. rewrite dsum_same.
exact: (EqT (Eq_sum_inv nn aa) (EqS (Eq_muldl C2 n a))).
Qed.

Lemma Tarski_th4':
  (forall x y z t,
    Sinfinite x -> Sinfinite y -> Sinfinite z -> Sinfinite t ->
    x <s y -> z <s t -> x \times z <s y \times t) -> 
  proposition_Z.
Proof.
move => hyp m mi.
have nse: nonempty Nat by exists \0c; apply: NS0.
move:(Eq_pow_mon1 m nse).
set n := functions _ _ => lmn.
apply: (Saleph_mon mi lmn).
have ni:= (Sinfinite_mon mi lmn).
move: (proposition_S ni); set a := substrate _;move => [pa pb pc].
case:(p_or_not_p (a \Eq n)) => ean; first exact: (Saleph_inv pa ean).
have nn: n \Eq (coarse n).
  move:(Eq_pow_inv (EqR m) (Saleph_double Saleph_Nat))(Eq_powpow m Nat C2).
  move => sa sb.
  exact:(EqT (EqT sa sb) (EqS (Eq_squareE n))).
have ai := proj1 pa.
move:(Eq_mul_mon1 n (Sinfinite_ne ai)) => le1.
move:(set_le_i2 (Eq_mul_mon1 a (Sinfinite_ne ni)) (Eq_setX2_S a n)) => le2.
case: (p_or_not_p (n \Eq (n \times a))) => eq1.
  case: pc; split => //; exact:(set_le_i2 le2 (EqS eq1)).
case: (p_or_not_p (a \Eq (n \times a))) => eq2.
  by case: pb; split; [ exact:(set_le_i2 le1 (EqS eq2)) | move/EqS].
have pi:= (Sinfinite_mon ni le1).
case:(proj2 (hyp _ _ _ _  ni pi (proj1 pa) pi  (conj le1 eq1) (conj le2 eq2))).
exact: (EqT (Eq_mul_inv nn (Saleph_square pa)) (EqS (Eq_square_mul n a))).
Qed.

  
Lemma Tarski_th5:
  (forall x y z,  Sinfinite x -> Sinfinite y -> Sinfinite z -> 
    dsum x z <s dsum y z -> x <s y)-> 
  proposition_Z.
Proof.
move => hyp n ni.
move: (proposition_S ni); set a := substrate _;move => [pa pb pc].
case:(p_or_not_p (n \Eq a)) => ean; first exact: (Saleph_inv pa (EqS ean)).
move: (Eq_sum_mono1 n a) (Eq_sum_mono1_bis n a) => le1 le2.
case: (p_or_not_p (a \Eq (dsum n a))) => eq1.
  case: pb; split => //;exact:(set_le_i2 le1 (EqS eq1)).
case: pc; apply:(hyp a n a (proj1 pa) ni (proj1 pa));rewrite(dsum_same a).
exact:(set_lt_i1 (conj le2 eq1) (Saleph_double pa)).
Qed.


Lemma Tarski_th5':
  (forall x y z,  Sinfinite x -> Sinfinite y -> Sinfinite z -> 
    x \times z <s y \times z -> x <s y)-> 
  proposition_Z.
Proof.
move => hyp n ni.
move: (proposition_S ni); set a := substrate _;move => [pa pb pc].
case:(p_or_not_p (n \Eq a)) => ean; first exact: (Saleph_inv pa (EqS ean)).
move:(Eq_mul_mon1 n (Sinfinite_ne (proj1 pa))) => le1.
move:(set_le_i2 (Eq_mul_mon1 a (Sinfinite_ne ni)) (Eq_setX2_S a n)) => le2.
case: (p_or_not_p (a \Eq (n \times a))) => eq2.
  case: pb;split => //;exact:(set_le_i2 le1 (EqS eq2)).
case: pc; apply:(hyp a n a (proj1 pa) ni (proj1 pa)).
exact:(set_lt_i1 (conj le2 eq2) (Saleph_square pa)).
Qed.



End CardinalSquare.

  
Module AFA.

(** ** Anti foundation axiom
 We study some properties that are forbidden by the axiom of foundation *)

Lemma afa_ex1 x: x <> \Po x.
Proof.
set A := Zo x (fun z => ~ inc z z) => h.
have aux: ~(inc A A).
  move /Zo_P => [pa pb]; apply: (pb); apply/Zo_P; split => //.
apply: (aux); apply:Zo_i => //; rewrite h; apply /setP_P; apply:Zo_S.
Qed.

Lemma afa_ex2 a b: a = singleton b -> b = doubleton emptyset a ->
  a = singleton (\Po a).
Proof. by move => pa pb; rewrite {2} pa setP_1 - pa - pb. Qed.

Lemma afa_ex2_inv a: a = singleton (\Po a) ->
  exists b,  a = singleton b /\ b = doubleton emptyset a.
Proof.
set b := \Po a => eq1; exists b; split => //.
by move: (setP_1 b); rewrite  - eq1.
Qed.

Lemma afa_ex3 a b c d:
  a = singleton b -> 
  b = (doubleton emptyset (singleton emptyset)) +s1 c +s1 d ->
  c = doubleton emptyset a -> d = singleton a ->
  a = singleton (\Po (\Po a)).
Proof. 
move => av bv cv dv; rewrite av setP_1 {1} bv -av; congr (singleton _).
set_extens t.
  move => h; apply/setP_P; case /setU1_P :h.
    case /setU1_P.
      case /set2_P => ->; fprops;apply : set1_sub; fprops.
    move => ->; rewrite - cv; fprops.
  move => ->; rewrite dv; apply : set1_sub; fprops.
move /setP_P => h.
case: (inc_or_not emptyset t) => ta; case: (inc_or_not a t) => tb.
- apply /setU1_P; left; apply /setU1_P; right; rewrite cv.
  by apply: extensionality => // => s; case /set2_P => ->.
- apply /setU1_P; left; apply /setU1_P; left; apply /set2_P; right.
  apply set1_pr => // s st; move: (h _ st); case /set2_P => // sa; case: tb; ue.
- apply /setU1_P; right; rewrite dv; apply set1_pr => // s st.
  move: (h _ st); case /set2_P => // sa; case: ta; ue.
- apply /setU1_P; left; apply /setU1_P; left; apply /set2_P; left.
  apply /set0_P => // s st; move: (h _ st); case /set2_P => sa.
    case: ta; ue.
  case: tb; ue.
Qed.


Lemma afa_ex3_inv a : a = singleton (\Po (\Po a)) ->
  exists b c d, [/\ 
    a = singleton b,
    b = (doubleton emptyset (singleton emptyset)) +s1 c +s1 d,
    c = doubleton emptyset a &
    d = singleton a].
Proof. 
set b := (\Po (\Po a)) => av; exists b.
move: (setP_1 b); rewrite - av; set c := doubleton emptyset a => h.
set d:= singleton a;exists c, d; split => //.
set_extens t.
  move => /setP_P; rewrite av; rewrite setP_1 - av => ct.
  case: (inc_or_not emptyset t);case: (inc_or_not a t) => ha hb.
  - apply: setU1_r; apply/setU1_P; right; set_extens u; first by move/ct. 
    by case/set2_P => ->.
  - apply: setU1_r;apply: setU1_r; apply/set2_P; right.
    by apply:(set1_pr hb) => u ut; case/set2_P:(ct _ ut) => // ua; case: ha;ue.
  - apply/setU1_P; right; apply:(set1_pr ha) => u ut.
   case/set2_P:(ct _ ut) => // ua; case: hb;ue.
  - apply: setU1_r;apply: setU1_r; apply/set2_P; left; apply/set0_P => u ut.
   case/set2_P:(ct _ ut) => hc; [ case: hb; ue | case: ha;ue].
case/setU1_P; last by move ->; apply /setP_P => u /set1_P ->;  apply: setP_Ti.
case/setU1_P; last by move ->;  rewrite - h; apply: setP_Ti.
case /set2_P => ->; first by apply: setP_0i.
by apply /setP_P => u /set1_P ->; apply:setP_0i.
Qed.

Lemma afa_ex4 x: x = gfunctions emptyset x <-> x = singleton emptyset.
Proof. by rewrite gfunctions_empty. Qed.

Lemma afa_ex5 X A: X = gfunctions X A <-> 
  (exists a f, [/\ A = singleton a, X = singleton f & f = singleton (J f a)]).
Proof.
split; last first.
  move => [a [f [Aa Xf fv]]].
  symmetry; rewrite {2} Xf.
  apply set1_pr.
    move: (simple_fct2 f a) => [sa sb _ _ _].
    apply /gfunctions_P1; rewrite fv sb; split => //.  
    move => t /set1_P; rewrite  Aa Xf => ->; apply: setXp_i; fprops.
  move => e /gfunctions_P1 [pa pb pc]; rewrite fv.
  apply: set1_pr1.
    apply /domain_set0P; rewrite pb Xf; fprops.
  move => z ze; move: (pc _ ze); rewrite Aa Xf. 
  by move /setX_P => [qa ] /set1_P qb/set1_P qc; rewrite - qa qb qc.
move => xsg.
case: (emptyset_dichot X) => xne.
  by empty_tac1 emptyset; rewrite {2} xsg xne gfunctions_empty; apply:set1_1.
move: xne => [f fX].
move: (fX); rewrite xsg; move => /gfunctions_P2 [pa pb pc].
set a := Vg f f.
have aA: inc a A.
  apply: pc; apply /range_gP => //; rewrite pb; ex_tac.
case: (equal_or_not A (singleton a)) => Aa.
  have pd: gfunctions X A = singleton f.
    apply: set1_pr; first by ue.
    move => z /gfunctions_P2 [qa qb qc].
    apply: fgraph_exten => //; first by ue.
    move => t td /=.
    have: inc (Vg z t) A by apply qc;  apply /(range_gP qa); ex_tac. 
    have: inc (Vg f t) A. 
       by apply pc; apply /(range_gP pa); rewrite pb - qb; ex_tac.  
    by rewrite Aa; move => /set1_P -> /set1_P ->.
  exists a; exists f;split => //.
  apply: set1_pr; first by apply: fdomain_pr1 => //; rewrite pb.
  move => e zf; rewrite (in_graph_V pa zf).
  by move: (domain_i1 zf); rewrite pb xsg pd => /set1_P ->.
have [b bA ba]: exists2 b, inc b A & b <> a. 
  ex_middle bad; case: Aa; apply: set1_pr => // z zA.
  ex_middle h; case: bad; ex_tac.
set F := Lg X (fun z => Yo (Vg z z = a) b a).
have fgf: fgraph F by rewrite /F; fprops.
have df: domain F = X by rewrite /F; aw.
have fx: inc F X. 
  rewrite xsg; apply /gfunctions_P2;split => //.
  by move => t /(range_gP fgf) [x qa ->]; rewrite /F LgV//; try ue; Ytac h.
case: (equal_or_not (Vg F F) a) => eq1.
   move: (eq1); rewrite {1} /F LgV//; Ytac0 => eba; by case: ba.
by move: (eq1); rewrite {1} /F LgV//; Ytac0; case.
Qed.

Lemma afa_ex6 X: X = gfunctions X X <-> 
  (exists2 x, X = singleton x & x = singleton (J x x)).
Proof.
split.
  move/afa_ex5 => [a [f [pa pb pc]]]; exists a => //.
  by rewrite pa in pb; rewrite {1 2} (set1_inj pb).
by move => [x pa pb]; apply /afa_ex5; exists x; exists x.
Qed.

Lemma afa_ex7 X: X = gfunctions X X <-> 
   X = singleton (singleton (singleton X)).
Proof.
apply (iff_trans (afa_ex6 X)).
have pa: forall t,  J t t = singleton (singleton t).
  by  move => t;  rewrite kpairE /kpair_def /singleton.
split.
  by move => [a ab]; rewrite pa => s; rewrite ab - s.
move => h; exists (singleton (singleton X)) => //. 
by rewrite pa - h.
Qed.

Lemma afa_ex8 X: X = singleton X -> X = gfunctions X X. 
Proof. by move => h; apply /afa_ex7; rewrite -h -h. Qed.

Lemma afa_ex9 X A: X = functions X A <-> 
  (exists a f, [/\ A = singleton a, X = singleton f & f = Lf (fun _ => a) X A]).
Proof.
have res: forall A a f t,
     function f ->  A = singleton a -> target f = A -> 
     inc t (source f) -> Vf f t = a.
  by move => B a f t ff -> tf tsf;move:(Vf_target ff tsf);rewrite tf => /set1_P.
split; last first. 
  move => [a [f [Aa Xf fv]]].
  symmetry; rewrite {2} Xf.
  have la: lf_axiom (fun _ : Set => a) X A by move =>  t _; rewrite Aa; fprops.
  have aux: function (Lf (fun _ : Set => a) X A) by apply: lf_function.
  apply: set1_pr.
    apply /functionsP; rewrite fv;red;saw. 
  move => e /functionsP [pa pb pc]; rewrite fv. 
  apply function_exten => //; aw; trivial => z ze; rewrite LfV//; last by ue. 
  by apply: (@res A). 
move => xsg.
case: (emptyset_dichot X) => xne.
  have aux:= (empty_function_tg_function A).
  by empty_tac1 ( empty_function_tg A); rewrite xsg xne; apply /functionsP.
move: xne => [f fX].
move: (fX); rewrite xsg; move => /functionsP [pa pb pc].
set a := Vf f f.
have aA: inc a A by rewrite -pc /a; Wtac.
case: (equal_or_not A (singleton a)) => Aa.
  have ha: functions X A = singleton f.
    apply: set1_pr;first by ue.
    move => z /functionsP [qa qb qc].
    apply: function_exten => //; (try ue); move => t td /=.
    have tx: inc t (source f) by rewrite pb - qb.
    by rewrite (res A a f t pa Aa pc tx) (res A a z t qa Aa qc td).  
  have pf: lf_axiom (fun _ => a) (functions X A) A by move => t _.
  have sf: source f = (functions X A) by ue.
  exists a, f;split => //.
  apply: function_exten; aw; trivial.
  - by apply: lf_function.
  - move => t tf /=; rewrite LfV//; [ by apply: (@res A) | ue ].
have [b bA ba]: exists2 b, inc b A & b <> a. 
  ex_middle bad; case: Aa; apply: set1_pr => // z zA.
  ex_middle h; case: bad; ex_tac.
set lam := (fun z => Yo (Vf z z = a) b a).
have ta: lf_axiom lam X A by rewrite /lam; move => t tX /=; Ytac h.
have fx: inc (Lf lam X A) X.
  rewrite {2} xsg; apply /functionsP;red;saw.
  by apply: lf_function.
by case: (equal_or_not (Vf (Lf lam X A)(Lf lam X A)) a) => eq1;
  move: (eq1); rewrite LfV//; rewrite {1} /lam; Ytac0.
Qed.

Lemma afa_ex10 X : X = functions X X <-> 
  (exists2 f, X = singleton f & f = triple X X  (singleton (J f f))).
Proof.
have aux: forall f, X = singleton f  -> 
  triple X X (singleton (J f f)) = Lf (fun _ : Set => f) X X.
  move => f Xf;move: (simple_fct2 f f); set g := (singleton (J f f)).
  move => [fgg sb sc sd se].
  have pa: lf_axiom (fun _ => f) X X by move => s _ ; rewrite Xf;apply: set1_1.
  apply function_exten; aw; trivial.
  + by rewrite Xf;apply: function_pr => //; rewrite sc.
  + by apply: lf_function. 
  + move => t tx /=; rewrite {1} /Vf. rewrite LfV//; aw.
    by move: tx; rewrite  Xf  => /set1_P => ->. 
apply: (iff_trans (afa_ex9 X X)); split.
  move => [a [f [xa xb xc]]]; exists f => //; move: xc.
  rewrite xb in xa; rewrite -(set1_inj xa) => {1} ->.
  by symmetry; apply: aux.
by move => [f Xf tf]; exists f, f;split => //; rewrite {1} tf; apply: aux.
Qed.

Lemma afa_ex11 X : X = functions X X <-> 
  X = singleton (singleton (singleton (singleton (singleton X)))).
Proof.
split.
  move /afa_ex10 => [f ->].
  by rewrite /triple ! kpairE /kpair_def - !/(singleton _) => <-.
move => h; apply /afa_ex10.
exists (singleton (singleton (singleton (singleton X)))); first exact.
by rewrite /triple !kpairE /kpair_def -! /(singleton _) -h  -! /(singleton _).
Qed.

Lemma afa_ex12 X : X = singleton X ->  X = functions X X.
Proof. by move => h; apply /afa_ex11; rewrite -!h. Qed.

End AFA.

(* Bourbaki proof thet bn and n2 are equipotent *)

Module NN2.


Lemma N2N_part1: cardinal (Nat) <=c cardinal (coarse Nat).
Proof.
have: sub ((singleton \0c) \times Nat) (coarse Nat).
  by apply:setX_Sl => bt /set1_P ->; apply:NS0.
by move/sub_smaller; rewrite (cardinal_indexedr Nat \0c).
Qed.

Definition finite_support f :=
   exists2 n, natp n & forall m, natp m -> n <=c m -> Vf f m = C0.
  
Definition dexpansions := Zo (functions Nat C2) finite_support.
                          
Definition wedge f g :=
  Lf (fun z => (Yo (evenp z) (Vf f (chalf z)) (Vf g (chalf z)))) Nat C2.
Definition wedge_i1 f :=
  Lf (fun z => (Vf f (cdouble z))) Nat C2.
Definition wedge_i2 f :=
  Lf (fun z => (Vf f (csucc (cdouble z)))) Nat C2.

Lemma wedge_exp f g:
  inc f dexpansions -> inc g dexpansions -> inc (wedge f g) dexpansions.
Proof.
move=> /Zo_P[/functionsP [ff sf tf] [bf bfN bfp]].
move=> /Zo_P[/functionsP [fg sg tg] [bg bgN bgp]].
have ax: lf_axiom (fun z => Yo (evenp z)
   (Vf f (chalf z)) (Vf g (chalf z))) Nat  C2.
  move => z zn /=; Ytac w; Wtac. 
    by rewrite sf; apply: NS_half.
  by rewrite sg; apply: NS_half.
apply:Zo_i.
  by rewrite/wedge; apply/functionsP; saw; apply:lf_function.
move: (Nmax_p1 (NS_double bfN) (NS_succ (NS_double bgN))).
set c := cmax _ _; move =>[cN cp1 cp2].
exists c => // m mN lcm.
rewrite /wedge LfV//.
move:(NS_half mN) => hN.
case:(cdouble_halfV mN) => ea.
  move:lcm; rewrite {1 2}ea (Y_true (even_double hN)) => ll.
  apply: bfp => //; apply/(double_monotone bfN hN); apply:(cleT cp1 ll).
move:lcm; rewrite {1 2}ea (Y_false (proj2 (odd_succ_double hN))) => ll.
have hy: cardinalp (cdouble (chalf m)) by apply:CS_nat; apply: NS_double.
move/(cleSSP (CS_nat (NS_double bgN)) hy) :(cleT cp2 ll). 
by move/(double_monotone bgN hN) => hx;apply:(bgp _ hN).
Qed.


Lemma wedge_i1p f g:
  inc f dexpansions -> inc g dexpansions ->
  wedge_i1 (wedge f g) = f.
Proof.
move=> /Zo_P[/functionsP [ff sf tf] [bf bfN bfp]].
move=> /Zo_P[/functionsP [fg sg tg] [bg bgN bgp]].
rewrite /wedge; set h := fun _ => _.
have ax: lf_axiom h Nat  C2.
  rewrite /h => z zn /=; Ytac w; Wtac. 
    by rewrite sf; apply: NS_half.
  by rewrite sg; apply: NS_half.
have ax2: lf_axiom (fun z => Vf (Lf h Nat C2) (cdouble z)) Nat C2.
  by move => x xN /=;move:(NS_double xN) => dN; rewrite LfV//; apply: ax.
apply: function_exten => //.
- by apply/lf_function.
- by rewrite/wedge_i1; aw.
- by rewrite/wedge_i1; aw.
- rewrite/wedge_i1; aw=> a aN;move:(NS_double aN) => dN; rewrite ! LfV//.
  by rewrite /h (Y_true (even_double aN)) (even_half aN).
Qed.


Lemma wedge_i2p f g:
  inc f dexpansions -> inc g dexpansions ->
  wedge_i2 (wedge f g) = g.
Proof.
move=> /Zo_P[/functionsP [ff sf tf] [bf bfN bfp]].
move=> /Zo_P[/functionsP [fg sg tg] [bg bgN bgp]].
rewrite /wedge; set h := fun _ => _.
have ax: lf_axiom h Nat  C2.
  rewrite /h => z zn /=; Ytac w; Wtac. 
    by rewrite sf; apply: NS_half.
  by rewrite sg; apply: NS_half.
have ax2: lf_axiom (fun z => Vf (Lf h Nat C2) (csucc (cdouble z))) Nat C2.
  by move => x xN /=;move:(NS_succ(NS_double xN)) => dN; rewrite LfV//; apply: ax.
apply: function_exten => //.
- by apply/lf_function.
- by rewrite/wedge_i2; aw.
- by rewrite/wedge_i2; aw.
- rewrite/wedge_i2; aw=> a aN;move:(NS_succ (NS_double aN)) => dN; rewrite !LfV//.
  by rewrite /h (Y_false (proj2 (odd_succ_double aN)))(odd_half aN).
Qed.

Lemma wedge_inverse h (f := wedge_i1 h) (g := wedge_i2 h):
  inc h dexpansions ->
  [/\ inc f dexpansions, inc g dexpansions &  (wedge f g) = h].
Proof.
move=> /Zo_P[/functionsP [fh sh th] [q qN qp]].
have axf: lf_axiom (fun z => Vf h (cdouble z)) Nat C2.
  by move => t tn /=; Wtac; rewrite sh; apply: NS_double.
have axg: lf_axiom (fun z => Vf h (csucc (cdouble z))) Nat C2
  by move => t tn /=; Wtac; rewrite sh; apply: NS_succ; apply: NS_double.
have ft: inc f dexpansions.
   rewrite /f/wedge_i1; apply: Zo_i. 
     by apply/functionsP; saw; apply: lf_function.
   exists q => // m mn mq; rewrite LfV// ; apply: qp; first by apply: NS_double.
   by apply: (cleT mq); apply: cle_n_doublen.
have gt: inc g dexpansions.
   rewrite /g/wedge_i2; apply: Zo_i. 
     by apply/functionsP; saw; apply:  lf_function.
   exists q => // m mn mq; rewrite LfV//; apply: qp.  
      by apply: NS_succ;apply: NS_double.
   exact:(cleT mq (cleT (cle_n_doublen mn) (cleS (NS_double mn)))).
split => //.
move:(wedge_exp ft gt) => /Zo_S/functionsP[fw sw tw].
apply: (function_exten fw fh); (try ue); rewrite sw => n nN.
move:(NS_half nN) => hN. 
have ax3: lf_axiom (fun z  => Yo (evenp z) (Vf f (chalf z)) (Vf g (chalf z)))
     Nat C2.
move => t tN /=; rewrite /f/g/wedge_i1 /wedge_i1 /wedge_i2.
  by move:(NS_half tN) => htN; Ytac x; rewrite LfV//; [  apply: axf | apply: axg ].
rewrite /wedge LfV//.
rewrite /f /g /wedge_i1 /wedge_i2=> //;Ytac hh; rewrite LfV//.
  by rewrite - (half_even hh).
by rewrite - (half_odd (conj nN hh)).
Qed.
  

  

Definition shift f := Lf(fun z => Vf f (csucc z)) Nat C2.
Definition size f := intersection (Zo Nat (fun n => 
   forall m, natp m -> n <=c m -> Vf f m = C0)).
Definition value f := csumb Nat (fun i => (Vf f i) *c (\2c ^c i)).

Lemma size_p f (s := size f): inc f dexpansions ->
  [/\ natp s, forall m, natp m -> s <=c m -> Vf f m = \0c &
   s = \0c \/ 
    [/\ natp (cpred s), csucc (cpred s) = s & Vf f (cpred s) <> \0c]].
Proof.
move=> /Zo_P [ff [q qN qp]]; rewrite  /s /size.
set E:=  Zo _ _.
have ha: sub E Nat by apply: Zo_S.
have hb: nonempty E by exists  q; apply: Zo_i.
move:(@inf_Nat E ha hb) =>[/Zo_P[qa qb] qc]; split => //.
case:(equal_or_not (intersection E) \0c) => ee; [by left | right].
move:(cpred_pr qa ee); set n := cpred _; move => [pN pv].
split => // fnz.
case:(cltNge (cpred_lt qa ee)).
have/ qc //: inc n E.
apply:(Zo_i pN) => m mN; case/cle_eqVlt; first by move => <-.
by move/(cleSltP pN); rewrite - pv; apply: qb.
Qed.

Lemma value_b f: inc f dexpansions ->
  value f = csumb (size f) (fun i => (Vf f i) *c (\2c ^c i)).
Proof.
move => ha; move: (size_p ha) =>[hb hc _].
rewrite /value {1}/csumb; set g := Lg _ _.
have  qa: sub (size f) (domain g).
  by rewrite /g; aw; trivial; apply: NS_inc_nat.
have qb:(forall i, inc i (domain g -s (size f)) -> Vg g i = \0c).
  rewrite /g;aw => i /setC_P[iN id]; rewrite LgV//.
  have ->: Vf f i = \0c.
    by  apply: hc => //;case: (NleT_el hb iN) => // /(NltP hb).
  by rewrite cprod0l.
rewrite (csum_zero_unit qa qb) /g; apply: csumb_exten => i ii; rewrite LgV//.
apply:(NS_inc_nat hb ii).
Qed.


Lemma value_nat f: inc f dexpansions -> natp (value f).
Proof.
move => ha; rewrite (value_b ha).
move: (proj31 (size_p ha)) => lN.
have fsl: finite_set (size f) by apply:finite_set_nat.
move/Zo_P:ha => [/functionsP[ff sf tf] _].
have ss: sub (size f) (source f) by  rewrite sf; apply:(NS_inc_nat lN).
apply: finite_sum_finite; saw.
have sC2N: sub C2 Nat by exact:(NS_inc_nat NS2).
hnf; aw  => t ti; rewrite LgV//;apply:NS_prod; first by apply:sC2N; Wtac.
by apply(NS_pow NS2); rewrite /natp - sf; apply:ss.
Qed.

Lemma shift_p1 f: inc f  dexpansions -> 
   inc (shift f) dexpansions /\ size (shift f) = cpred (size f).
Proof.
move => fd.
move:(size_p fd); set fs:= size _; move =>[sfa sfb sfc].
move:fd=> /Zo_P [/functionsP[ff sf tf] [q qN qp]].
have ax: lf_axiom (fun z => Vf f (csucc z)) Nat C2.
  move => t /NS_succ tN; Wtac; ue.
have sd: inc (shift f) dexpansions.
  apply: Zo_i. 
    by rewrite/shift;apply/functionsP; saw; apply: lf_function.
  rewrite/shift; exists q => // m mN lmn; rewrite  !LfV//.
  move:(NS_succ mN). move:(cleT lmn (cleS mN)) => ra rb.
  by apply: qp.
move:(size_p sd); set s := size _; move =>[sa sb sc]; split => //.
have aux2: fs <=c s -> s = \0c.
  move => le; case: sc => // - [pN pv]; rewrite /shift LfV//  pv.
  case;  exact:(sfb _ sa le).
case: sfc.
  by move => sfz; rewrite sfz cpred0; apply: aux2; rewrite sfz; apply:cle0n.
set r := cpred fs;  move =>[rN rv fv].
case:(NleT_ell sa rN) => // csr.
  case:(equal_or_not r \0c) => rz.
    by case: (nesym (proj2(cle_ltT (cle0n sa) csr))).
  move:(cpred_pr rN rz) => [mN mv].
  move: csr; rewrite mv; move/(cltSleP mN) => le1.
  case: fv; move:(sb _ mN le1); rewrite /shift LfV//; ue.
case:(equal_or_not s \0c) => sz.
  by case: (nesym (proj2(cle_ltT (cle0n rN) csr))).
by move/(cleSltP rN): csr; rewrite  rv => /aux2.
Qed.

Lemma shift_val f: inc f  dexpansions -> 
  value f = Vf f \0c +c \2c *c (value  (shift f)).
Proof.
move => fd.
move:fd=> /Zo_P [/functionsP[ff sf tf] [q qN qp]].
have ax: lf_axiom (fun z => Vf f (csucc z)) Nat C2.
  move => t /NS_succ tN; Wtac; ue.
have qb: quasi_bij csucc Nat (Nat -s1 \0c).
  split.
  - by move => t tn; apply/setC1_P; split; [ apply: NS_succ | apply: succ_nz].
  - by move => u v /CS_nat cu /CS_nat cv; apply: csucc_inj.
  - move => y /setC1_P [yN ynz]; move:(cpred_pr yN ynz)=> [qa qb].
    by exists (cpred y).
rewrite {2} /value cprod2Dn; set s1 := csumb _ _.
pose g i := (Vf f i *c \2c ^c i).
have ->: s1 = csumb Nat (fun i => g (csucc i)).
  apply: csumb_exten => i iN.
  by rewrite /shift /g LfV//; rewrite cprodC - cprodA cpow_succ.
have hu: ~ inc \0c (Nat -s1 \0c) by  case/setC1_P.
have hv: ((Nat -s1 \0c) +s1 \0c) = Nat by apply: setC1_K; apply: NS0.
have ->: Vf f \0c = g \0c.
  rewrite /g cpowx0 cprod1r //; apply: CS_nat;apply:(NS_inc_nat NS2).
  rewrite- [\2c] / C2; Wtac; rewrite sf; apply:NS0.
rewrite -(csum_Cn2 g qb) csumC - csumA_setU1//; ue.
Qed.

Lemma value_inj f g: inc f  dexpansions -> inc g dexpansions->
   value f = value g -> f = g.
Proof.
move: f g.
suff: forall n, natp n -> forall f g,  
   size f <=c n -> size g <=c n ->
   inc f dexpansions -> inc g dexpansions ->  value f = value g -> f = g.
  move => H f g ft gt.
  move:(size_p ft) (size_p gt) => /proj31 sN /proj31 sN' sv.
  move: (Nmax_p1 sN sN') =>[qa qb qc].
  exact:(H _ qa f g qb qc ft gt sv).  
apply: Nat_induction.
  move => f g /cle0 s1z /cle0 s2z ft gt sv.
  move:(size_p ft)(size_p gt) =>[qa qb qc][qd qe qf].
  move: ft gt => /Zo_S /functionsP [ff sf tf]/Zo_S /functionsP [fg sg tg].
  apply: (function_exten ff fg); (try ue); rewrite sf => t tN.
  have sa: size f <=c t by  rewrite s1z; apply: cle0n.
  have sb: size g <=c t by  rewrite s2z; apply: cle0n.
  by rewrite (qb _ tN sa) (qe _ tN sb). 
move => n nN Hrec f g ls1 ls2 ft gt sv.
move: (shift_p1 ft)(shift_p1 gt) => [f1t sf1] [f2t sg2].
move:(proj31 (size_p ft)) (proj31 (size_p gt)) => sfN sgN.
have h1: size (shift f) <=c n.
  rewrite sf1; case: (equal_or_not  (size f) \0c) => qa. 
     by rewrite qa cpred0 ; apply:cle0n.
  move: (cpred_pr sfN qa) => [qc qd].
  apply/(cleSSP (CS_nat qc) (CS_nat nN)); ue.
have h2: size (shift g) <=c n.
  rewrite sg2; case: (equal_or_not  (size g) \0c) => qa. 
     by rewrite qa cpred0 ; apply:cle0n.
  move: (cpred_pr sgN qa) => [qc qd].
  apply/(cleSSP (CS_nat qc) (CS_nat nN)); ue.
move: (shift_val ft) (shift_val gt).
rewrite csumC (csumC (Vf g \0c)). 
move:(value_nat f1t) (value_nat f2t).
set v1 := value _ ; set v2 := value _  => vfN vgN eq1 eq2.
move:(value_nat ft) => vN.
move/Zo_S:ft => /functionsP[ff sf tf].
move/Zo_S:gt => /functionsP[fg sg tg].
have aux t: inc t C2 -> t <c \2c.
  case/set2_P => -> -; [ apply: clt_02 | apply: clt_12].
have fsm: Vf f \0c <c \2c.
  have /aux //: inc (Vf f \0c) C2 by Wtac; rewrite sf; apply: NS0.
have gsm: Vf g \0c <c \2c.
  have /aux //: inc (Vf g \0c) C2 by Wtac; rewrite sg; apply: NS0.
move:(NS_lt_nat fsm NS2) (NS_lt_nat gsm NS2) => fsN gsN.
have d1p: cdivision_prop (value f) \2c v1 (Vf f \0c) by split. 
have d2p: cdivision_prop (value g) \2c v2 (Vf g \0c) by split. 
rewrite - sv in d2p.
move: (cdivision_unique vN NS2 vfN fsN vgN gsN card2_nz d1p d2p) =>[ra rb].
move:(Hrec _ _ h1 h2 f1t f2t ra) => rc.
apply: (function_exten ff fg); (try ue); rewrite sf => x xN.
case: (equal_or_not x \0c) => xz; first by rewrite xz; apply: rb.
move: (cpred_pr xN xz) =>[pN pv].
move:(f_equal (Vf ^~ (cpred x)) rc); rewrite /shift ! LfV; trivial.
- by rewrite - pv.
- by move => t /NS_succ tN; Wtac; ue.
- by move => t /NS_succ tN; Wtac; ue.
Qed.


Lemma value_surj x: natp x -> exists2 f, inc f dexpansions &  x = value f.
Proof.
move: NS0 => zn nN; move:(cleR (CS_nat nN)).
move: x nN {1 3} x; apply: Nat_induction.
  move => x /cle0 ->; pose f :=  (Lf (fun _ => C0) Nat C2).
  have ax:  lf_axiom (fun _  => C0) Nat C2 by move =>  t _ /=; fprops.
  have ft: inc f dexpansions.
    rewrite/f;apply:Zo_i. 
      by apply/functionsP; saw; apply: lf_function.
    exists \0c; [ apply: NS0 | move => y yN _ ; rewrite LfV//].
  exists f => //.
  move:(size_p ft) => [qa qb qc].
  case: qc; first by move => sz; rewrite (value_b ft) sz csumb0.
  move => [sz pv]; case; rewrite/f LfV//.
move => n nN Hrec x /cle_eqVlt; case; last by move/(cltSleP nN); apply: Hrec.
move => ->.
have sN := NS_succ nN.
move: (Hrec _  (cle_halfSn_n nN)) => [f fp fvv].
set r := Yo (evenp (csucc n)) C0 C1.
have rc2: inc r C2  by  rewrite /r; Ytac h; fprops.
have  xv: csucc n = r +c cdouble (chalf (csucc n)).
  rewrite /r; Ytac h; first by rewrite - (half_even h) Nsum0l.
  have hh: natp (cdouble (chalf (csucc n)))by apply: NS_double; apply: NS_half.
  rewrite csumC - (Nsucc_rw  hh); exact: (half_odd (conj sN h)).
pose g := Lf (fun z => Yo (z = \0c) r (Vf f (cpred z))) Nat C2.
move/Zo_P: fp => [ /functionsP [ff sf tf] [q qa qb]].
have ax: lf_axiom (fun z => Yo (z = \0c) r (Vf f (cpred z))) Nat C2.
  move => z zN /=; case:(equal_or_not z \0c) => zz; Ytac0 => //.
  by Wtac; rewrite sf; apply: NS_pred.
have gt: inc g dexpansions.
  apply: Zo_i.
    by rewrite /g;apply/functionsP; saw; apply: lf_function.
  exists (csucc q); fprops => m mN lemq; rewrite /g LfV//.
  move: (clt_leT (succ_positive q) lemq) => /proj2/nesym mz.
  move:(cpred_pr mN mz) => [sa sb]; Ytac0; apply: (qb _ sa).
  apply/(cleSSP (CS_nat qa) (CS_nat sa)); ue.
have g0: Vf g \0c  = r by rewrite /g LfV//; Ytac0.
exists g. exact.
rewrite (shift_val gt) xv fvv g0.
move:(shift_p1 gt) => /proj1 /Zo_S/functionsP [fs ss ts].
do 3 apply: f_equal; apply: (function_exten ff fs); try ue. 
rewrite sf /shift /g => v vN; move:(NS_succ vN) => svN; rewrite !LfV//.
  by rewrite (Y_false (@succ_nz v)) cpred_pr2.
by move => t tN /=;  move:(NS_succ tN) => stN; rewrite LfV//; apply: ax.
Qed.

Definition valuef := (Lf value dexpansions Nat).
Definition function_n2_n :=
  Lf (fun p => value (wedge (Vf (inverse_fun valuef) (P p))
                            (Vf (inverse_fun valuef) (Q p)))) (coarse Nat) Nat.

Lemma value_bij : bijection_prop valuef dexpansions Nat.
Proof.
rewrite/valuef; saw.
apply: (lf_bijective value_nat value_inj value_surj).
Qed.  

Lemma bn_nn: bijection_prop function_n2_n (coarse Nat) Nat.
Proof.
move: value_bij => [bv sv tv].
have ax0 := value_nat.
have ax1 x: natp x -> inc (Vf (inverse_fun valuef) x) dexpansions.
  move => xn; rewrite - sv; apply: inverse_Vis => //; ue.
have ax2 p: inc p (coarse Nat) ->inc
     (wedge (Vf (inverse_fun valuef) (P p)) (Vf (inverse_fun valuef) (Q p)))
     dexpansions.
  by move => /setX_P [pp pa pb]; apply: wedge_exp; apply: ax1.
rewrite /function_n2_n; saw; apply: lf_bijective.
- by move => p pp; apply: ax0; apply: ax2.
- move => u v uc vc; move/(value_inj (ax2 _ uc) (ax2 _ vc)) => sv1.
  move/setX_P: uc =>[pa pb pc];move/setX_P: vc =>[pd pe pf].
  move: (ax1 _ pb) (ax1 _ pc) (ax1 _ pe) (ax1 _ pf) =>  qa qb qc qd.
  move:(wedge_i1p qa qb) (wedge_i1p qc qd); rewrite sv1 => -> eqa.
  move:(wedge_i2p qa qb) (wedge_i2p qc qd); rewrite sv1 => -> eqb.
  move:(f_equal (Vf valuef) eqa); rewrite inverse_V ? inverse_V //; try ue.
  move:(f_equal (Vf valuef) eqb); rewrite inverse_V ? inverse_V //; try ue.
  by move => ra rb; apply: pair_exten.
- move => y yN; 
  have ytc: inc y (target valuef) by ue.
  move: (inverse_V  bv ytc) (inverse_Vis bv ytc).
  set x := (Vf (inverse_fun valuef) y) =>[qa qb].
  move: qb; rewrite {1} /valuef; aw => xd.
  move: qa; rewrite {1} /value LfV// => vx.
  move: (wedge_inverse xd).
  set x1 := (wedge_i1 x); set x2 := (wedge_i2 x).
  move =>[x1p x2p x12].
  move:(wedge_i1p x1p x2p) (wedge_i2p x1p x2p) (wedge_exp x1p x2p).
  set x3 := wedge x1 x2; move => x3a x3b  x3t.
  have x1v: (Vf (inverse_fun valuef) (value x1)) = x1.
    have ->: value x1 = Vf valuef x1 by rewrite /valuef LfV.
    by apply: (inverse_V2 bv); ue.
  have x2v: (Vf (inverse_fun valuef) (value x2)) = x2.
    have ->: value x2 = Vf valuef x2 by rewrite /valuef LfV.
    by apply: (inverse_V2 bv); ue.
  set z := J (value x1) (value x2).
  exists z; first by apply:setXp_i; apply: ax0.
by rewrite /z; aw; rewrite  {1} x1v x2v x12.
Qed.

Lemma bn_nn_inj : injection_prop function_n2_n (coarse Nat) Nat.
Proof. by move: bn_nn =>[[ha _] hb hc]. Qed.


Lemma B_N2N: Nat \Eq (coarse Nat).
Proof.
move:  bn_nn_inj =>[ha hb hc].
move: (inj_source_smaller ha); rewrite hb hc => hd.
apply/card_eqP; exact: (cleA N2N_part1 hd).
Qed.

End NN2.

(* alternate proof *)
Lemma card_Nintcc_alt a b: a <=N b -> 
  cardinal (Nintcc a b) = csucc (b -c a).
Proof.
move=> [aN bN ab].
have ca := (CS_nat aN).
have H0:   (Nintcc a a) = singleton a.
  apply: set1_pr.
    apply/(Nint_ccP1 aN aN); split; apply:(cleR ca).
  by move => v /(Nint_ccP1 aN aN) [va vb]; apply: cleA.
have H1 n: natp n ->
 (Nintcc a (csucc (a +c n))) = (Nintcc a (a +c n))+s1 (csucc (a +c n)). 
  move => nN; move: (NS_sum aN nN) => sN; move: (NS_succ sN) => ssN.
 set_extens t.
    move/(Nint_ccP1 aN ssN) =>[aet]; case/cle_eqVlt; first by move->; fprops.
    by move/(cltSleP  sN) => ti; apply:setU1_r; apply/(Nint_ccP1 aN sN).
  case/setU1_P. 
    move/(Nint_ccP1 aN sN)=>[sa sb]; apply/(Nint_ccP1 aN ssN); split => //.
    exact: (cleT sb (cleS sN)).
  move ->;apply/(Nint_ccP1 aN ssN); split => //.
  exact: (cleT (csum_M0le n ca) (cleS sN)).
  by  apply/(cleR (CS_nat ssN)).
have H2 n: natp n -> ~ inc (csucc (a +c n)) (Nintcc a (a +c n)).
  move => nN; move:  (NS_sum aN nN) => sN.
  by move /(Nint_ccP1 aN sN) /proj2; apply:cltNge; apply:cltS.
move: (cdiff_pr ab) (NS_diff a bN) => {2} <- cN.
move: (b-c a) cN; clear b bN ab.
apply: Nat_induction; first by rewrite (csum0r ca) H0 succ_zero cardinal_set1.
move => n nN Hrec.
by rewrite (csum_nS _ nN) (H1 _ nN) (csucc_pr (H2 _ nN)) Hrec.
Qed.



Lemma succ_study (r: relation) x
  (r' := fun a b => r a b /\ a <> b)
  (Ap := fun y A => forall t, inc t A <->  [/\ r x t, r t y & t <> x])
  (Ax:= fun y => exists A, Ap y A)
  (Ay := fun y => choose (Ap y))
  (ly := fun y => the_least (graph_on r (Ay y))):
  worder_r r ->
  (forall y, r' x y -> Ax y) ->
  [/\ (r x x -> ~ (exists y, r' x y) -> forall t, r t t -> r t x),
      (forall y, r' x y -> r' x (ly y)) ,
      (forall y, r' x y -> forall t, r' x t -> r (ly y) t) &
      (forall y y', r' x y -> r' x y' ->  ly y = ly y')].
Proof.
move => wor; move: (wor) => [[ha hb hc] hd] h2.
have h3: forall y, r' x y -> Ap y (Ay y).
  by move => y /h2 ax; apply: choose_pr.
have h4: forall y, r' x y -> inc y (Ay y).
  move => y ya; move:(h3 _ ya) => h; apply/h.
  by move: ya => [rxy /nesym xny]; split => //; move: (hc _ _ rxy)=> [].
have h5: forall y, r' x y -> has_least (graph_on r (Ay y)).
   move => y ya; move: (h3 _ ya)  (h4 _ ya)  => yb yc.
   apply:hd; [by move => t /yb [/hc []] | ex_tac ].
have h6: forall y, r' x y ->  order_on (graph_on r (Ay y)) (Ay y).
   move => y ya; move: (h3 _ ya) => yb.
   have rr:{inc (Ay y), reflexive_r r} by move => t /yb [/hc []].
   by move:(wordering_pr wor rr) => [[qa _] qb].
have h7:forall y, r' x y -> least (graph_on r (Ay y)) (ly y).
  move => y ya; move: (h6 _ ya) => [oR sR]; apply: the_least_pr => //.
  exact: h5.
have h8: forall y, r' x y -> r' x (ly y).
  move => y ya; move: (h7 _ ya); rewrite /least (proj2 (h6 _ ya)).
  by move =>[ /(h3 _ ya) [ua _ /nesym ub] _]; split.
have h9: forall y, r' x y -> forall t, r' x t -> r (ly y) t.
   move => y ya t ta.
   move: (h7 _ ya); rewrite /least (proj2 (h6 _ ya)); move => [_ yb].
   move: (yb _ (h4 _ ya)) => /graph_on_P1 [_ _ yc].
   have ryy:=(proj2 (hc _ _ (proj1 ya))).
   have rtt:= (proj2 (hc _ _ (proj1 ta))).
   case: (worderr_total wor ryy rtt) => cyt.
     exact (ha _ _ _ yc cyt).
   have: inc t (Ay y) by move:ta => [t1 /nesym t2];apply/(h3 _ ya). 
   by move/yb => /graph_on_P1 [_ _].
split => //.
+ move => rxx ney t rtt.
  case:(equal_or_not x t) => exy; first by rewrite exy.
  case: (worderr_total wor rxx rtt) => // rxt.
  by case: ney; exists t; split. 
+ move => y y' ya yb.
  exact (hb _ _  (h9 _ ya _ (h8 _ yb)) (h9 _ yb _ (h8 _ ya))).
Qed.

Lemma limit_study (r: relation) y B 
  (C := B +s1 y) 
  (R := (graph_on r C))
  (x := supremum R B):
  (forall a, inc a B <-> r a y /\ a <> y) ->
  worder_r r -> r y y ->
     [/\ (least_upper_bound R B x /\ r x y),
         (B = emptyset -> forall t, r t t -> r y t), 
         ( x <> y ->
          [/\ inc x B, x = the_greatest (graph_on r B),
           (forall z, r x z -> r z y -> z = x \/ z = y) &
           (forall z, r z z -> r z x \/ r y z)]) &
         (x = y -> forall B1, nonempty B1 -> finite_set B1 -> sub B1 B -> 
           inc (the_greatest (graph_on r B1)) B)].
Proof.
move => hB wor ryy.
move:(wor) => [ [ha hb hc] _].
have hd: {inc B, reflexive_r r} by  move => t /hB [/hc []].
have he: {inc C, reflexive_r r}.
   move => t /setU1_P []; [by apply:hd | by move -> ].
have sBC: sub B C by apply:sub_setU1. 
have yC: inc y C by rewrite /C; fprops.
have srB:= (graph_on_sr hd).
move:(wordering_pr wor he) => [woR sr].
have oR := proj1 woR.
have pa: sub B (substrate (graph_on r C)) by rewrite graph_on_sr.
have uy: upper_bound (graph_on r C) B y.
  split; first by rewrite sr.
  move => t tB;apply /graph_on_P1; split => //; first by apply sBC.
  by move/(hB t): tB => [].
have hs:has_supremum (graph_on r C) B.
  by apply:(worder_hassup woR pa); exists y. 
have xp: least_upper_bound R B x by apply: (supremum_pr1 oR).
move:(supremum_pr1 oR hs) => /(lubP oR pa) []; rewrite -/x => h1 h2.
move: (h2 _ uy) => /graph_on_P1 [_ _ rxy].
have pb: forall t, inc t B -> r t x.
    by move => t /(proj2 h1) /graph_on_P1 [].
have pc: x <> y ->
  [/\ inc x B, x = the_greatest (graph_on r B),
     (forall z, r x z -> r z y -> z = x \/ z = y) &
     (forall z, r z z -> r z x \/ r y z)].
  move => xz. 
  have xB: inc x B by apply/hB. 
  move:(supremum_pr1 oR hs) => /(lubP oR pa) [hh _].
  move: hh; rewrite -/x; move => [_ hx].
  have orB: order (graph_on r B) by apply: (order_from_rel B (proj1 wor)).
  have xgr: x = the_greatest (graph_on r B).
    symmetry;apply: (the_greatest_pr2 orB); hnf; rewrite srB; split => //.
    move => t tB; move/hB: (tB)=> [qa qb]; apply /graph_on_P1; split => //.
    by move:(hx _ tB) => /graph_on_P1 [].
  have hh:forall z, r z z -> r z x \/ r y z.
    move => z rzz; case (equal_or_not z y) => ezy; first by rewrite ezy; right.
    case: (worderr_total wor ryy rzz) => czy; first by right.
    have zB: inc z B by apply/hB.
    by move: (hx _ zB) =>  /graph_on_P1 [ _ _ rzx]; left.
  split => // t t1 t2; case (equal_or_not t y) => ty; first by right.
  have tB: inc t B by apply /hB.
  by move:(hx _ tB) => /graph_on_P1 [_ _ t3]; rewrite (hb _ _ t1 t3); left.
have pd: B = emptyset -> forall t, r t t -> r y t.
   move => be t rtt.
   case (equal_or_not t y) => ty; first by ue.
   case: (worderr_total wor ryy rtt) => // czy. 
   empty_tac1 t; by apply/hB. 
split => // exy B1 neB1 fsB1  sb1.
have hf : {inc B1, reflexive_r r} by move => t/sb1 /hd.
move:(wordering_pr wor hf) => [wos ss].
move:(worder_total wos) => tos.
have ss1: sub B1 (substrate (graph_on r B1)) by rewrite ss.
move: (finite_subset_torder_greatest tos fsB1  neB1 ss1). 
rewrite -{2} ss (iorder_substrate (proj1 tos)) => hgt.
move:(the_greatest_pr (proj1 tos) hgt) => []; rewrite ss => r0 _.
by apply: sb1.
Qed.

(** * Lemmas that do not use cardinal or ordinal numbers *)
Module Misc1.

(** There is a distributive law between [powerset] and [intersection2] *)

Lemma powerset_mono A B: sub A B -> sub (\Po A)(\Po B).
Proof.
move=> sAB t /setP_P ta; apply/setP_P; apply:(sub_trans ta sAB).
Qed.

Lemma union_monotone3 A B:
  sub A B -> sub (union A) (union B).
Proof. 
move=> sAB t /setU_P [y ty yA]; apply/setU_P;exists y => //; fprops.
Qed.

Lemma intersection_greatest A B x: 
  sub x A -> sub x B -> sub x (A \cap B).
Proof. move=> xA xB t tx; apply /setI2_P; split;fprops. Qed.

Lemma powerset_inter: {morph powerset : A B / A \cap B}.
Proof.
move => A B; apply: extensionality.
  apply: intersection_greatest; apply: powerset_mono. 
     apply: subsetI2l.
  apply:subsetI2r.
move=> x /setI2_P[] /setP_P xpA /setP_P xpB; apply /setP_P. 
by apply: intersection_greatest.
Qed.



(* original implementation *)
Lemma worder_decreasing_finite_orig  r r' (f:fterm):
  worder r -> worder r' ->
  (forall i, inc i (substrate r) -> inc (f i) (substrate r')) ->
  (forall i j, glt r i j -> glt r' (f j) (f i)) ->
  finite_set (substrate r).
Proof. 
move=> wor wor' ta finc; move: (proj1 wor') => or'.
move: Nat_order_wor=> [wob bsr].  
case: (isomorphism_worder3 wob wor); last first.
  move => [x]; rewrite bsr; move => xn [g [pa pb]].
  have ss:=(@sub_segment Nat_order x).
  rewrite (iorder_sr (proj1 wob) ss) (segment_Nat_order xn) => fp _.
  have cc:cardinal (Nint x)= cardinal (substrate r) by apply/card_eqP; exists g.
  by rewrite /finite_set - cc; apply: finite_Nint.
move =>[g [sr isg]].
have gsi:=(order_morphism_sincr  isg).
move: isg => [or  _ [fg sg tg] incfg].
have sg1: source g = Nat by rewrite sg bsr.
move: sr => [sr1 _].
set Y := fun_image (Imf g) f.
have Ysr: sub Y  (substrate r').
  move => t /funI_P [z /(Imf_P fg) [x1 x1g x1p] ->]; apply: ta.
  rewrite x1p; apply: sr1; Wtac.
have yi n: natp n -> inc (f (Vf g n)) Y.
  by move => nN;apply/funI_P;exists (Vf g n)=> //;Wtac; rewrite sg1.
have neY: nonempty Y by exists (f (Vf g \0c)); apply (yi _ NS0).
move:(worder_prop wor' Ysr neY) => [y /funI_P [z za zb] yb].
move/(Imf_P fg): za => [n nN np]; rewrite sg1 in nN.
have lt1: glt Nat_order n (csucc n).
  move:(cltS nN) => [qa qb].
  split => //; apply /Nat_order_leP; split => //; apply: (NS_succ  nN).
move:(finc _ _ (gsi _ _ lt1)); rewrite - np - zb => lt2.
have /yb lt3: inc (f (Vf g (csucc n))) Y by apply:yi; apply:NS_succ. 
order_tac.
Qed.

(** Two isomorphic segments of a well-ordered set are equal 
Original proof  *)


Lemma segments_iso1 r A B: worder r -> sub A B ->
  segmentp r A -> segmentp r B ->
  (induced_order r B) \Is (induced_order r A) -> A = B.
Proof.
move => woa AB sA sB.
move => [f [ora orb [ [[ff injf] sjf] sf tf] isf]].
have oa: order r by move: woa => [o _].
have As: sub A (substrate r) by apply: sub_segment1.
have Bs: sub B (substrate r) by apply: sub_segment1.
move: sf tf; rewrite ! iorder_sr // => sf tf.
rewrite - sf in injf isf.
have ta: lf_axiom (Vf f) B B.
    move=> t tx; apply: AB; rewrite - tf; Wtac; ue.
set g := Lf (Vf f) B B.
have fg: function g by apply: lf_function.
have rg: (Imf g = A).
  rewrite - tf;set_extens t. 
    move /(Imf_P fg)=> [u];rewrite /g lf_source => uc; rewrite LfV// => ->; Wtac; ue.
  move/(proj2 sjf) =>[u usf].
  rewrite sf in usf;move=> ->; apply /(Imf_P fg).
  exists u; rewrite /g; aw; trivial;rewrite LfV//.  
have sr: segmentp  (induced_order r B) (Imf g).
  rewrite rg; hnf; rewrite iorder_sr//;split => //.
  move => x y xA leyx; move: (iorder_gle1 leyx).
  move: sA xA; rewrite /segmentp; move=>[_]; apply.
have om: order_morphism g (induced_order r B)(induced_order r B).
  hnf; split => //; first by rewrite /g iorder_sr//;saw.
  rewrite /g; hnf;aw;  move=> x y xB yB /=; rewrite ! LfV//.
  move:(iorder_gle0P r (ta _ xB) (ta _ yB)) => xx.
  hnf in isf; rewrite sf in isf.
  apply: (iff_trans (isf _ _ xB yB)).
  rewrite - sf in xB yB.
  move: (Vf_target ff xB) (Vf_target ff yB); rewrite tf => f1a f2a.
  apply: (iff_trans (iorder_gle0P r f1a f2a)).
  by symmetry.
have wob:= (induced_wor woa Bs).
have gi:= (unique_isomorphism_onto_segment wob sr om).
symmetry;move: rg; rewrite gi; rewrite iorder_sr // surjective_pr0 //; aww.
by move: (identity_fb B) => [_ ok].
Qed.



Lemma segments_iso2 a A B: worder a ->
   inc A  (segments a) -> inc B  (segments a)  ->
   (induced_order a A) \Is (induced_order a B) -> A = B.
Proof.
move=> woa As Bs.  
move: (worder_total (segments_worder woa)) => [or].
rewrite (proj2 (sub_osr _)) => tor; move: (tor _ _ As Bs).
move: As Bs;move/(inc_segmentsP woa)=> As /(inc_segmentsP woa) Bs.
case; move /sub_gleP=> [_ _ sAB] oi.
  move: (orderIS oi) => oi'; apply: (segments_iso1 woa)=>//.
symmetry; apply: (segments_iso1 woa)=>//.
Qed.

(* original proof *) 
Lemma isomorphic_subset_segment r X:
  worder r -> sub X (substrate r) -> 
  exists2 w, segmentp r w &  
    (induced_order r X) \Is (induced_order r w).
Proof. 
move => wor asr.
move: (proj1 wor) => or.
have woi :=(induced_wor wor asr).
case: (isomorphism_worder2 woi wor).
- move => [f isf]; exists (substrate r). 
    apply: substrate_segment.
  by exists f; rewrite (iorder_substrate or).
- rewrite (iorder_sr or asr). move => [x xa].
  have ha:sub (segment (induced_order r X) x) X by apply: sub_segment2.
  rewrite /seg_order(iorder_trans _ ha); move =>[f fiso].
  move:(order_isomorphism_siso fiso) => fsi.
  move: fiso => [hb _ hc hd].
  move:hc; rewrite (iorder_sr or (sub_trans  ha asr)); move =>[bf sf tf].
  pose E := Zo (substrate r) (fun z => glt r (Vf (inverse_fun f) z) z). 
  have xsr := asr _ xa.
  have Esr: sub E (substrate r) by apply: Zo_S.
  have neE: nonempty E.
    exists x; apply: (Zo_i xsr).
    rewrite -tf in xsr;move: (inverse_Vis bf xsr); rewrite sf =>/segmentP.
    by move/iorder_gle2.
  move: (worder_prop wor Esr neE) =>[y /Zo_P[ysr lt1] yl].
  set z :=   (Vf (inverse_fun f) y).
  move:(arg1_sr (proj1 lt1)) => zsr.
  suff /yl eZ: inc z E by move: (not_le_gt or eZ  lt1).
  have ytf: inc y (target f) by ue.
  apply: (Zo_i zsr). rewrite -/z.
  set t := (Vf (inverse_fun f) z).
  move: (inverse_V bf ytf); rewrite -/z => yv.
  rewrite -tf in zsr;move: (inverse_Vis bf zsr); rewrite -/z -/t => tsf.
  move: (inverse_V bf zsr); rewrite -/z -/t => zv.
  move: lt1; rewrite -/z - yv -{1} zv => lt2.
  by move/ (fsi t z tsf (inverse_Vis bf ytf)): lt2 => /iorder_gltP [_ _ ].
- move => [x xE /orderIS ww].
  by exists (segment r x) => //; apply: (segment_segment _ or). 
Qed.

(** The following gives a well-ordering on [doubleton a b], even when [a=b] *)

Definition example_worder a b := (tripleton (J a a) (J b b)  (J a b)).

Lemma example_worder_gleP a b x y: 
    related  (example_worder a b) x y <->
    [\/ (x = a /\ y = a),  (x = b /\ y = b) |  (x = a /\ y = b)].
Proof.
split; first by case /set3_P => h;rewrite(pr1_def h)(pr2_def h); in_TP4.
case => [] [->  ->]; apply /set3_P; in_TP4.
Qed.

Lemma example_is_worder a b:
  worder_on (example_worder a b) (doubleton a b).
Proof. 
have gc:sgraph (example_worder a b).
  move => t /set3_P; case => ->; fprops.
have subs: substrate (example_worder a b) = doubleton a b.
  set_extens x. 
    case/(substrate_P gc)=> [] [y].
      move / (example_worder_gleP a b x y); case; case => ->; fprops.
    move /(example_worder_gleP a b y x); case; case => _ ->; fprops.
  case /set2_P=> h; have aux: (related (example_worder a b) x x)
    by apply/(example_worder_gleP a b x x); in_TP4.
    substr_tac.
  substr_tac.
have pa: related (example_worder a b) a a by  apply/example_worder_gleP; in_TP4.
have pb: related (example_worder a b) b b by  apply/example_worder_gleP; in_TP4.
have pc: related (example_worder a b) a b by  apply/example_worder_gleP; in_TP4.
have oc: (order (example_worder a b)). 
  split => //.
    by red;rewrite subs => y /set2_P [] ->. 
  move=> x y z/example_worder_gleP; case; move => [ -> ->]//.
    move /example_worder_gleP; case; move => [ h ->] //.
  move=> x y /example_worder_gleP; case;move => [ -> ->] //.
  by move /example_worder_gleP; case; case.
split; [split; [  exact | ] | exact ].
move => x xab nex.
case: (inc_or_not a x)=> hyp.
  exists a; red; rewrite (iorder_sr oc xab); split=>//.  
    move=> y yx; apply /(iorder_gle0P _ hyp yx); apply /example_worder_gleP.
    move: (xab _  yx); rewrite subs; case /set2_P; in_TP4.
move: nex=> [y yx]; exists y; red;rewrite (iorder_sr oc xab); split=>//.
move => z zx; apply /(iorder_gle0P _ yx zx); apply /example_worder_gleP.
rewrite subs in xab.
case /set2_P: (xab _  yx) => yb; first by case: hyp; rewrite -yb.
case /set2_P: (xab _  zx) => zb; first by case: hyp; rewrite - zb.
in_TP4.
Qed.


(** Example of inductive sets (another one is in the main text)  *)

Lemma inductive_example1 A F: sub A (\Po F) ->
  (forall S, (forall x y, inc x S -> inc y S -> sub x y \/ sub y x) ->
    inc (union S) A) ->
  inductive (sub_order A).
Proof. 
move=> Ap ih X Xs [oX tX];exists (union X).
have  [oi si ] := (sub_osr A).
move: tX; rewrite iorder_sr// => tX;rewrite si in Xs.
have uA: inc (union X) A.
  by apply: ih; move=> x y xX yX; move: (tX _ _ xX yX); case =>h;
   move: (iorder_gle1 h) => /sub_gleP [_ _ h1]; [left | right].
split; first by rewrite si.
by move=> y yX; apply /sub_gleP;split; [apply: Xs | exact | apply: setU_s1].
Qed.

(* A weird  comparison *)
Definition weird_comp x y z :=
  sub x y /\ [\/ x = C0 /\ y = C1, x = C1 /\ y = C2 , x = y | y = z].

Lemma weid_comp_prop:
  [/\ forall x y z, weird_comp x y z -> weird_comp y x z -> x = y,
     forall x y z, weird_comp x y z -> weird_comp x x z /\ weird_comp y y z,
     forall x y z, weird_comp x y z -> weird_comp y z z -> weird_comp x z z &
      exists z, ~ (order_r (fun x y => weird_comp x y z))].
Proof.
have ra: forall x y z, weird_comp x y z -> weird_comp y x z -> x = y.
  by move => x y z [qa _][qb _]; apply: extensionality.
have rb: forall x y z, weird_comp x y z -> weird_comp x x z /\ weird_comp y y z.
  by move => x y z [qa _]; split; split => //; constructor 3.
have rc: forall x y z, weird_comp x y z -> weird_comp y z z -> weird_comp x z z.
  move => x y z [qa qb][qc qd]; split; first by apply: (sub_trans qa qc). 
  by constructor 4.
pose f z := (fun x y => weird_comp x y z). 
have rd: forall z, transitive_r (f z) -> order_r (f z).
  move => z af; split => // x y; [apply: ra | apply: rb].
have re: ~ transitive_r (f C3).
  have ha: f C3 C0 C1 by  split; [fprops | constructor 1].
  have hb: f C3 C1 C2.
     split; first by move => t /set1_P ->; apply/set2_P; left.
     by constructor 2.
  move:C2_ne_C01 C3_ne_C012  => [/nesym na nb][_ _ /nesym nc].
  move => h; move: (h C1 C0 C2 ha hb) => [_]; case => //.
  - move => [_] //.
  - by move => [hd _]; case: C0_ne_C1.
by split => //; exists C3; case => tr _ _; case:re.
Qed.


Lemma order_indep (p: property) (r:= fun x y => p x):
  order_r r <-> forall x, ~(p x).
Proof.
split.
  move =>[ha hb hc] x0 px0.
  have py:forall y, (p y) by move => y;exact:(proj2 (hc x0 y px0)).
  have qy: forall y, x0 = y by move => y; exact:(hb _ _ px0 (py y)).
  by case:(C0_ne_C1); rewrite -(qy C0) -(qy C1).
move => pf; split.
- by  move => a b c /pf.
- by move => a b /pf.
- by move => a b /pf.
Qed.


Lemma not_ord_example (r:= fun A X Y => [/\ sub X Y, sub X A & sub Y A]):
   (forall A, order_r (r A)) /\ (forall Y, ~ order_r(fun A X => r A X Y)).
Proof.
split.
  move => A; split.
  - move => y x z [ha hb hc][hd he hf]; split => //; apply: (sub_trans ha hd).
  - by move => x y [ha hb hc][hd he hf]; apply: extensionality.
  - move => x y [ha hb hc]; split; split => //.
move => Y [ha hb hc].
have r1 Z: r Z Z Y -> Z = Y by  move => [qa qc]; apply: extensionality.
have r2: r (Y +s1 Y) emptyset Y by split; fprops.
move: (hc _ _ r2) => [/r1 hh /r1 hhh]; empty_tac1 Y; rewrite -{2} hh; fprops.
Qed.


Lemma ord_sup_prop E: ordinal_set E ->
  exists! x, ordinalp x /\
   (forall y,  x <=o y <-> (ordinalp y /\ ordinal_ub E y)).
Proof.
move=> alo; set p := fun x: Set => _; apply /unique_existence;split.
  have ou:= (OS_sup alo).
  exists (\osup E); split => // y; split.
    move => h.
    have oy:= (proj32 h).
    split => //; move=> i iE; exact (oleT (ord_sup_ub alo iE) h).
  by move=> [oy aly]; apply:ord_ub_sup.
have p1: forall x, p x -> ordinal_ub E x.
  move=> t [ox Ex].
  by move: (oleR ox); rewrite (Ex t); move => [_].
have p2: forall x y, p x -> ordinalp y ->
  (ordinal_ub E y) -> x <=o y.
  move=> x1 y1 [ox opf] oy  h; rewrite opf; split => //.
move=> x y fx fy.
exact: (oleA (p2 _ _ fx (proj1 fy) (p1 _ fy)) (p2 _ _ fy (proj1 fx) (p1 _ fx))).
Qed.


Lemma cardinal_supremum1 x:
  cardinal_set x ->
  exists! b, [/\ cardinalp b,
    (forall a, inc a x -> a <=c b) &
    (forall c, cardinalp c ->  (forall a, inc a x -> a <=c c) -> 
      b <=c c)].
Proof. 
move=> alc.
move: (CS_sup alc) (card_sup_ub alc) => pa pb.
apply /unique_existence; split.  
  by exists (union x); split => // y cy; apply:(card_ub_sup).
move=> u v [cu up1 up2][cv vp1 vp2].
exact: (cleA (up2 _ cv vp1) (vp2 _ cu up1)).
Qed.


Theorem cardinal_supremum2 x:
  fgraph x -> cardinal_fam x ->
  exists!b, [/\ cardinalp b,
    (forall a, inc a (domain x) ->(Vg x a) <=c b) & 
    (forall c, cardinalp c -> 
      (forall a, inc a (domain x) -> (Vg x a) <=c c) -> 
      b <=c c)].
Proof. 
move=> fg alx.
have aly: cardinal_set (range x).
  by move=> a /(range_gP fg) [z zd ->]; apply: alx.
move /unique_existence: (cardinal_supremum1 aly) => [[b [cb bp1 bp2]] _].  
apply /unique_existence;split. 
  exists b; split =>//.
     move=> a adx; apply: bp1; by apply: inc_V_range. 
  move=> c cc hc; apply: bp2=> //. 
  move=> a  => /(range_gP fg) [d dd ->].
  by apply: hc.
move=> u v [cu up1 up2][cv vp1 vp2].
exact:(cleA (up2 _ cv vp1) (vp2 _ cu up1)).
Qed.

End Misc1.


(** This property has a much shorter proof than the one given here*)
Lemma aleph_pr13 n: ordinalp n ->
  \aleph (osucc n) <c \2c ^c (\2c ^c (\aleph n)).
Proof.
move => on.
have son:= OS_succ on.
have cas:= CS_aleph son.
have con := CS_aleph on.
have icy:= CIS_aleph on.
have ->: \2c ^c \aleph n = \2c ^c (coarse (\aleph n)).
  rewrite - {1} (csquare_inf icy).
  by apply: cpow_pr; fprops; rewrite /coarse cprod2_pr1; aw.
apply: (clt_leT (cantor cas)).
apply: (cpow_Meqle card2_nz); rewrite - card_setP - (aleph_succ_pr2 on).
apply: surjective_cle. 
set E := \aleph n.
pose f X := Yo ((worder X) /\ cardinal (substrate X) = E) (ordinal X) E.
set T := (aleph_succ_comp n).
have zT: inc E T.
  apply /setC_P; split; last by exact: (ordinal_irreflexive (proj1 con)).
  by move: (oclt (aleph_pr10c on)) => /oltP0 [].
have oas:= OS_aleph son.
have ta: lf_axiom f (\Po (coarse E)) (aleph_succ_comp n).
  move => t te; rewrite /f; Ytac h; last by exact.
  move: h => [h1 h2].
  have oot:= (OS_ordinal h1).
  case: (oleT_el oas oot) => // le1.
    move: (ocle1 le1); rewrite (cardinal_of_ordinal h1).
    rewrite h2 (card_card cas) => le2. 
    case: (cleNgt le2 (aleph_lt_ltc (oltS on))). 
  move /oltP0: le1 => [_ _ lt1].
  apply /setC_P; split => // le3.
  have: (ordinal t) <o E by apply /(oltP (proj1 con)).
  move /(ocle2P con oot).
  by rewrite (cardinal_of_ordinal h1) h2; move => [_].
exists (Lf f (\Po (coarse E)) T);saw.
apply: lf_surjective => // x /(aleph_succ_P1 on)  [pa pb].
have ox:= proj32 pa.
have pg: cardinal x = E.
  apply: cleA; last by move: (ocle1 pa);rewrite (card_card con).
  move /(ocle2P cas ox): pb; rewrite - (cnextE on) => h.
  exact:(cnext_pr4 (proj1 icy) h).
have [g [bg sg tg]]: exists g, bijection_prop g x E.
  by apply /card_eqP; rewrite (card_card con).
have wox:=(ordinal_o_wor ox).
have pc: substrate (ordinal_o x) = source g by rewrite ordinal_o_sr.
move: (bg) => [[fg _] _].
have pd: function (ext_to_prod g g) by apply: ext_to_prod_f.
have pe: sub (ordinal_o x) ((source g) \times  (source g)).
  rewrite -pc;  apply: sub_graph_coarse_substrate; fprops.
have pf: sub (ordinal_o x) (source (ext_to_prod g g)).
  by rewrite /ext_to_prod; aw.
move: (order_transportation bg (conj (proj1 wox) pc)).
set o := Vfs _ _ => isg.
exists o.
  apply /setP_P => t /(Vf_image_P pd pf)  [u uo ->]. 
  move: (pe _ uo) => up;  rewrite (ext_to_prod_V2 fg fg up). 
  move: up => /setX_P [_ p1 p2]; apply /setXp_P;split => //; Wtac.
have es1: ordinal_o x \Is o by exists g.
move: (worder_invariance es1 wox) => woE.
have eq: x = ordinal o by symmetry;apply: ordinal_o_isu2 => //; apply: orderIS.
rewrite /f Y_true //; split => //.
rewrite - (cardinal_of_ordinal woE) - eq //.
Qed.

Module IncFun.

Lemma card_sincreasing_rev_Nat (r := Nat_order) :
   functions_sincr r  (opp_order r) = emptyset.
Proof.
move: Nat_order_wor =>[wor sr]; move: (proj1 wor) => or.
apply/set0_P => [f /Zo_P[ha hb]].
move:(strict_increasing_fun_reva hb).
rewrite /opp_order (igraph_involutive (proj41 or)).
move => [_ _ [ff sf tf] fi].
have hc i: inc i (substrate Nat_order) ->
       inc (Vf f i) (substrate Nat_order).
  rewrite -{1} sf - tf => isg; Wtac.
move: (worder_decreasing_finite wor wor hc fi); rewrite sr => fn.
by move: (finite_not_infinite_set fn infinite_Nat).
Qed.


Lemma card_increasing_rev1_Nat (r := Nat_order) :
  Nat <=s (functions_incr r  (opp_order r)).
Proof.
move: Nat_order_wor =>[wor sr]; move: (proj1 wor) => or.
pose c v  := constant_function Nat Nat v.
have ha v: natp v -> inc (c v) (functions_incr r (opp_order r)).
  move => vN.
  have sc: source (c v) = Nat by rewrite /c/constant_function; aw.
  have tc: target (c v) = Nat by rewrite /c/constant_function; aw.
  move: (constant_constant_fun Nat vN) => cp.
  have qa: substrate r = source (c v) by ue.
  have qb: substrate r = target (c v) by ue.
  apply/Zo_P; split.
     rewrite(proj2 (opp_osr or)) sr.
     by move: (proj1 cp) => fc; apply/functionsP.
  move:(proj2 (constant_fun_increasing or or qa qb cp)).
  by move/(decreasing_fun_reva).
pose F := Lf c Nat (functions_incr r (opp_order r)).
have injf: injection  F.
  apply: lf_injective => // a b aN bN sv.
  move: (f_equal (Vf ^~ \0c) sv).
  by rewrite  /c (constant_V aN NS0) (constant_V bN NS0).
by exists F; rewrite /F;split => //; aw.
Qed.

Lemma card_increasing_rev2_Nat f (r := Nat_order) :
  inc f (functions_incr r  (opp_order r)) ->                            
  exists2 n, natp n & forall i, natp i -> n <=c i -> Vf f i = Vf f n.
Proof.
move: Nat_order_wor =>[wor sr]; move: (proj1 wor) => or.
case/Zo_P.
rewrite(proj2 (opp_osr or)) sr; move/functionsP => [ff sf tf].
move/(increasing_fun_reva).
rewrite /opp_order (igraph_involutive (proj41 or)) => - [ _ _ _ df].
have Ha: forall i j, natp i -> natp j -> i <=c j -> Vf f j <=c Vf f i.
   move => i j iN jN lik.
   have /df/Nat_order_leP/proj33// : gle r i j  by apply/Nat_order_leP.
pose p n := exists2 m, natp m & n = Vf f m.
have zN := NS0.
set v := Vf f \0c.
have pv: p v by exists \0c.
have vN: natp v by rewrite /natp /v; Wtac; ue.
move: (least_int_prop vN pv); set m := least_ordinal _ _.
move => [mn [n nN mv] hyp]; exists n => //.
move => i iN lin.
move: (Ha n i nN iN lin); rewrite - mv => le1.
have nw: natp (Vf f i) by  apply: (NS_le_nat le1).
have pw: p (Vf f i)  by exists i.
exact: (cleA le1 (hyp _ nw pw)).
Qed.

Definition least_stationary f := 
  intersection (Zo Nat
      (fun n => forall i, natp i -> n <=c i -> Vf f i = Vf f n)).
Definition  rest_to_stationary f := 
  restriction2 f (csucc (least_stationary f)) Nat.


Lemma card_increasing_rev3_Nat f (r := Nat_order)
  (n := least_stationary  f):
  inc f (functions_incr r  (opp_order r)) ->                            
  natp n /\ forall i, natp i -> n <=c i -> Vf f i = Vf f n.
Proof.
move => /card_increasing_rev2_Nat [m qa qb].
rewrite /n/least_stationary ; set E := Zo _ _.
have seN: sub E Nat by apply: Zo_S.
have nee: nonempty E by exists m; apply: Zo_i.
move: (inf_Nat seN nee). rewrite -/n; move => [/Zo_P[nN qc] qd]; split => //.
Qed.

Definition functions_incr_Nat_aux :=
  unionb (Lg Nat (fun n => (functions (csucc n) Nat))).

            
Lemma card_increasing_rev4_Nat f (r := Nat_order):
  inc f (functions_incr r  (opp_order r)) ->                            
  restriction2_axioms f (csucc (least_stationary f)) Nat.
Proof.
move: Nat_order_wor =>[wor sr]; move: (proj1 wor) => or.
move => ha.
move: (proj1 (card_increasing_rev3_Nat ha)) => nN.
case/Zo_P: ha.
rewrite(proj2 (opp_osr or)) sr; move/functionsP => [ff sf tf] _; split.
- done.
- rewrite sf; exact: (NS_inc_nat (NS_succ nN)).
- by rewrite tf.
- by rewrite - tf; apply: fun_image_Starget1.
Qed.

Lemma card_increasing_rev5_Nat f (r := Nat_order):
  inc f (functions_incr r  (opp_order r)) ->                            
  inc (rest_to_stationary f)  functions_incr_Nat_aux.
Proof.
move => ha.
move: (proj1 (card_increasing_rev3_Nat ha)); rewrite /natp => nN.
apply/setUb_P; aw; ex_tac; rewrite LgV//.
by apply/functionsP; apply:restriction2_prop; apply: card_increasing_rev4_Nat.
Qed.


Lemma card_increasing_rev6_Nat (r := Nat_order):
  (functions_incr r  (opp_order r)) <=s functions_incr_Nat_aux.
Proof.
exists (Lf rest_to_stationary (functions_incr r (opp_order r))
            functions_incr_Nat_aux).
saw; apply: lf_injective.
   apply: card_increasing_rev5_Nat.
move => u v hu hv.
move: (card_increasing_rev3_Nat hu).
move: (card_increasing_rev3_Nat hv).
set nu := (least_stationary u); set nv := (least_stationary v).
move =>[qa qb ][qc qd].
move: (card_increasing_rev4_Nat hu)(card_increasing_rev4_Nat hv) => axu axv.
rewrite/rest_to_stationary => sva.
move: (f_equal source sva). rewrite/restriction2; aw.
move /(csucc_inj (CS_nat qc) (CS_nat qa)) => sn.
move: Nat_order_wor =>[wor sr]; move: (proj1 wor) => or.
case/Zo_P: hu; case/Zo_P: hv.
rewrite(proj2 (opp_osr or)) sr; move/functionsP => [fv sv tv] _.
move/functionsP => [fu su tu] _.
apply: function_exten => //; try ue.
have Ha i: i <=c nu -> Vf u i = Vf v i.
  move => li; move: (f_equal (Vf ^~ i) sva).
  have iu: inc i (csucc nu) by apply/ NleP.
  have iv: inc i (csucc nv) by ue.
  by rewrite (restriction2_V axu iu)(restriction2_V axv iv).
rewrite su => i iN.
case: (NleT_ee iN qc); first by apply: Ha.
move => le1; move: (le1); rewrite  sn => le2.
rewrite (qd _ iN le1) (qb _ iN le2) Ha sn //; fprops.
Qed.

  
Lemma card_functions_incr_Nat_aux:
  countable_set (functions_incr_Nat_aux).
Proof.
apply: countable_union; rewrite /allf;aw; first by apply: countable_Nat.
move  => i iN; rewrite LgV//; apply/countableP; rewrite cpow_pr1.
rewrite cardinal_Nat (card_card (CS_succ i)).
by apply: (cpow_inf1 _ (NS_succ iN)); apply: CIS_aleph0. 
Qed.


Lemma card_increasing_rev_Nat (r := Nat_order):
  cardinal (functions_incr r  (opp_order r)) = aleph0.
Proof.
move /eq_subset_cardP1:  card_increasing_rev6_Nat => /= => ha.
move /eq_subset_cardP1:  card_increasing_rev1_Nat; rewrite - aleph0_pr1 => hc.
move /countableP:  card_functions_incr_Nat_aux => hb.
exact: (cleA (cleT ha hb) hc). 
Qed.
  

Lemma card_increasing_Nat_aux f (r := Nat_order) :
  inc f (functions_incr r r) <->
  inc f (functions Nat Nat) /\
   forall i j, i <=c j -> natp j ->  Vf f i <=c Vf f j.
Proof.
move: Nat_order_wor =>[[or _] sr].
split.
  move => /Zo_P []; rewrite sr => ha hb; split => // i j lij jN.
  have la: gle Nat_order i j.
     apply/Nat_order_leP; split => //; apply: (NS_le_nat lij jN).
  by move: hb  => [_ _ _  fp]; move: (fp i j la) => /Nat_order_leP/proj33.
move =>[qa qb]; move/functionsP: (qa) => qc.
apply: Zo_i; [ ue | split => //; first ue].
move: qc =>[ff sf tf].
move => i j /Nat_order_leP[iN jN le1]; apply/Nat_order_leP.
move: (qb _ _ le1 jN) => qd.
by split => //; rewrite /natp; Wtac; rewrite sf.
Qed.
  
  
Lemma card_increasing_Nat (r := Nat_order) :
  functions_incr r r =c  functions_sincr r r.
Proof. 
move: Nat_order_wor =>[[or _] sr].
set Q1:= functions_incr r r.
set Q2:= functions_sincr r r.
have Hb f: inc f Q2 <->
   inc f (functions Nat Nat) /\
   forall i j, i <c j -> natp j ->  Vf f i <c Vf f j.
  split.
    move => /Zo_P []; rewrite sr => ha hb; split => // i j [lij nij] jN.
    have la: glt Nat_order i j.
      split=> //; apply/Nat_order_leP; split => //; apply: (NS_le_nat lij jN).
    move: hb  => [_ _ _  fp].
    by move: (fp i j la) => [/Nat_order_leP/proj33 xa xb].
  move =>[qa qb]; move/functionsP: (qa) => qc.
  apply: Zo_i; [ ue | split => //; first ue].
  move: qc =>[ff sf tf].
  move => i j [/Nat_order_leP[iN jN le1] nij].
  move: (qb _ _ (conj le1 nij) jN) => [qd qe]. 
  split => //; apply/Nat_order_leP.
  by split => //; rewrite /natp; Wtac; rewrite sf.
pose subi f:=  Lf (fun i=> (Vf f i) -c  i) Nat Nat.
have Hi0:forall f, inc f Q2 -> 
   [/\ (forall i, natp i -> natp (Vf f i)),
    (forall i j, i <c j -> natp j  -> (Vf f i) <c (Vf f j)) &
    (forall i, natp i -> (i <=c (Vf f i)))]. 
  move=> f /Hb [/functionsP [ff sf tf] sif].
  have ha i: natp i -> natp (Vf f i) by  rewrite /natp - {1} sf => isf; Wtac.
  split => // i iN.
  have sN:= NS_succ iN; have lisi := cltS iN.
  have hq j: j <c csucc i -> natp (Vf f j).
     move => ll; apply: ha; apply: (NS_lt_nat ll sN).
  have hr a b : a <c b -> b <c csucc i -> Vf f a <c Vf f b.
     move => sa sb; apply: sif => //; apply: (NS_lt_nat sb sN).
  by apply: (strict_increasing_prop1 sN hq hr).
have Hi3:forall f, inc f Q2 ->
    lf_axiom (fun i  =>  (Vf f i) -c i) Nat Nat.
  move=> f fQ2; move: (Hi0 _ fQ2) => [p1 p2 p3].
  by move: (Hi0 _ fQ2) => [sa sb sc] o oN; apply: NS_diff; apply: p1.
have Hi1:forall f, inc f Q2 -> inc (subi f) (functions Nat Nat).
   move=> f fQ2;apply /functionsP; rewrite /subi; hnf;saw.
   by apply: lf_function; apply: Hi3.
have Hi2:forall f, inc f Q2 -> inc (subi f) Q1.
  move=> f fQ2; apply /card_increasing_Nat_aux.
  split; first by apply: Hi1.
  move: (Hi0 _ fQ2) (Hi3 _ fQ2)  => [p1 p2 p3] ta.
  move => i j lij jN.
  move: (NS_le_nat lij jN) => iN.
  rewrite /subi !LfV//.
  have sN:= NS_succ jN; have lisi := cltS jN.
  have hq k: k <c csucc j -> natp (Vf f k).
     move => ll; apply: p1; apply: (NS_lt_nat ll sN).
  have hr a b : a <c b -> b <c csucc j -> Vf f a <c Vf f b.
     move => sa sb; apply: p2 => //; apply: (NS_lt_nat sb sN).
  by apply: (@strict_increasing_prop2 (csucc j) (Vf f) sN hq hr).
set (G:= Lf subi Q2 Q1).
have Hi4:function G by rewrite / G; apply: lf_function. 
pose addi f := Lf (fun i=> (Vf f i) +c i) Nat Nat.
have pa:forall f, inc f (functions Nat Nat) ->
    lf_axiom (fun i  => (Vf f i) +c i) Nat Nat.
  move=> f /functionsP [ff sf tf] t tN.
   apply: (NS_sum _ tN); rewrite /natp; Wtac; rewrite sf.
have pa2 f: inc f (functions Nat Nat) ->
    inc  (addi f) (functions Nat Nat).
  move=> fE; rewrite /addi; apply /functionsP;hnf;saw.
  by apply: lf_function;  apply: pa.
have pa3: forall f, inc f Q1 -> inc (addi f) Q2.
  move=> f / card_increasing_Nat_aux [fe1e2 incf]; move: (pa _ fe1e2) => ax.
  apply /Hb; split; first by  apply:pa2.
  move => i j  lij jN.
  have iN:= (NS_lt_nat lij jN).
  move/functionsP: fe1e2  => [ff sf yf].
  have aux: natp (Vf f j)by  rewrite /natp; Wtac; ue.
  rewrite/addi !LfV//.
  exact: (csum_Mlelt aux (incf _ _  (proj1 lij) jN)) lij.
set (F:= Lf addi Q1 Q2).
have ff: function F by apply: lf_function.
have cGF: G \coP F by rewrite /G/F; split => //; aw.  
have cFG: F \coP G by rewrite /G/F; split => //; aw.  
have c1i: (G \co F = identity (source F)).
apply: function_exten; aw; [fct_tac | apply: identity_f| done  | |  ].
    by  rewrite /G/F; aw. 
  move => x xsf /=;rewrite (idV xsf); aw.
  rewrite corresp_s in xsf.
  have aQ2: inc (addi x) Q2 by apply: pa3.
  have xx: inc x (source (Lf addi Q1 Q2)) by aw.
  rewrite /F compfV// LfV// /G LfV// /addi/subi.  
  move: (xsf) => / card_increasing_Nat_aux [/functionsP [fx sx tx] icx].
  apply: function_exten; aw =>//.
     apply: lf_function; apply: Hi3; apply: pa3 =>//.
  move: (Hi3 _ aQ2)=> ta2.
  have H a :  natp a -> natp (Vf x a) by rewrite /natp => aN; Wtac.
  move=> a aN /=.
   rewrite LfV// LfV//; first  by apply: (cdiff_pr1 (H a aN) aN).  
   move  => t tN /=; apply: (NS_sum (H _ tN) tN).
have c2i: (F \co G = identity (source G)).
  apply: function_exten; [fct_tac | fprops |  by aw | by rewrite /F/G; aw | ].
  rewrite /G; aw => x xQ2 /=;rewrite idV //.
  have qQ1: inc (subi x) Q1 by apply: Hi2.
  move: (xQ2) => /Hb  [/functionsP [fx sx tx] icx].
  have xx: inc x (source (Lf subi Q2 Q1)) by aw.
  rewrite compfV// LfV// /F LfV// /addi/subi.  
  symmetry; apply: function_exten; aw; trivial.
    apply: lf_function; apply: pa; apply: Hi1=> //.  
  have ta3:= (Hi3 _ xQ2).
  have ta2:=(pa _ (Hi1 _ xQ2)).
  rewrite sx => i isx;  rewrite ! LfV // cdiff_rpr //.
  exact: (proj33 (Hi0 _ xQ2) i isx).
move: (bijective_from_compose cGF cFG c1i c2i) => /proj31.
by move/card_bijection; rewrite /F; aw.
Qed.


Lemma card_sincreasing_Nat (r := Nat_order) :
  functions_sincr r r =c  functions Nat Nat.
Proof. 
rewrite - card_increasing_Nat.
set fNN := functions Nat Nat.
pose D f := fun i => Yo (i = \0c) (Vf f \0c) (Vf f i -c (Vf f (cpred i))).  
pose S f := fun i =>  csumb (csucc i) (Vf f). 
have Hu f: inc f  fNN -> natp (Vf f \0c).
  move=> /functionsP [ff sf tf].
  rewrite /natp; Wtac; rewrite sf; apply: NS0.
have Ha f: inc f  fNN -> (S f \0c) = Vf f \0c.
  move/Hu /CS_nat => cc.
  rewrite /S (induction_on_sum _ NS0) csum_trivial0 csum0l//.
have Hb f n:  natp n -> S f (csucc n) = (S f n) +c Vf f (csucc n) .
  by move=> nN; rewrite /S (induction_on_sum _ (NS_succ nN)).
have Hc f : inc f fNN ->lf_axiom (S f) Nat Nat.
  move => fnn; move: (Ha _ fnn)  (Hu _ fnn) => eq1 nn1.
  move/functionsP: fnn =>[ff sf tf].
  apply: Nat_induction; first by rewrite eq1.
  move => n nN Hr; rewrite (Hb _ _ nN); apply: (NS_sum Hr).
  rewrite /natp; Wtac; rewrite sf; apply: (NS_succ nN).
have Hd f:   inc f  fNN -> inc (Lf (S f) Nat Nat) (functions_incr r r).
  move => ff; apply/card_increasing_Nat_aux.
  have ax: lf_axiom (S f) Nat Nat by move => t tn; apply: Hc.
  split; first  by apply/functionsP; saw; apply: lf_function.
  move => i j lij  jN.
  have iN: natp i by apply: (NS_le_nat lij jN).
  rewrite ! LfV//; move: j jN lij; apply: Nat_induction.
    move/cle0 => ->; rewrite (Ha _ ff); exact: (cleR (CS_nat (Hu _ ff))).
  move => n nN Hrec; case /cle_eqVlt.
    by move ->; apply cleR; apply: CS_nat; apply: ax; apply: (NS_succ nN).
  move/(cltSleP nN) => /Hrec le1; apply: (cleT le1).
  by rewrite (Hb _ _ nN); apply: csum_M0le; apply: CS_nat; apply: ax. 
have Hv f: inc f  (functions_incr r r) ->  lf_axiom (D f) Nat Nat.
  move=> /card_increasing_Nat_aux [/functionsP [ff sf tf] fi]  t tnN.
  rewrite /D; Ytac h; first by  Wtac; rewrite sf; apply:NS0.
  by apply: NS_diff; rewrite /natp;Wtac; rewrite sf; apply:NS_succ.
have He f: inc f (functions_incr r r) -> inc (Lf (D f) Nat Nat)  fNN.
  by move/ Hv => aw; apply/functionsP; saw; apply: lf_function.
pose D1 := fun f => (Lf (D f) Nat Nat). 
apply/card_eqP; exists (Lf D1 (functions_incr Nat_order Nat_order) fNN).
have ns0 := NS0.
saw; apply: lf_bijective.
- by  apply: He.
- move => u v hu hv sva.
  move: (hu)=> /card_increasing_Nat_aux [/functionsP [fu su tu] fiu].
  move: (hv)=> /card_increasing_Nat_aux [/functionsP [fv sv tv] fiv].
  apply: function_exten; [ done | done | ue | ue |].
  move: (Hv _ hu) (Hv _ hv) => axu axv.
  rewrite su; apply: Nat_induction.
    move: (f_equal (Vf ^~ \0c) sva); rewrite /D1 ! LfV //.
    by rewrite /D; Ytac0; Ytac0.
  move => n nN Hrec.
  move: (NS_succ nN) => snN.
  move: (f_equal (Vf ^~ (csucc n)) sva); rewrite /D1 !LfV// /D.
  rewrite (Y_false (@succ_nz _)) (Y_false (@succ_nz _)).
  rewrite (cpred_pr1 (CS_nat nN)) => eq.
  rewrite - (cdiff_pr (fiu _ _ (cleS nN) snN)).
  by rewrite - (cdiff_pr (fiv _ _ (cleS nN) snN)) eq Hrec.
- move => y yf; move: (Hd y yf) => uu; ex_tac.  
  have ax2:=  (Hc y yf).
  move/functionsP: (yf) =>[fy sy ty].
  move: (He _ uu) => /functionsP[fx sx tx].
  apply:function_exten;[ done | done | by rewrite /D1;aw | by rewrite /D1;aw| ].
  have ax1:=  (Hv _ uu).
  rewrite sy => t tN; move: (NS_pred tN)=> stn.
  rewrite /D1 ! LfV // /D !LfV//; Ytac ww.
     by rewrite ww Ha.
  have qa: natp (Vf y t) by  rewrite /natp; Wtac.
  have qb: natp (S y (cpred t)) by apply:ax2.
  move: (proj2 (cpred_pr tN ww)) => eq1.
  rewrite {2} eq1  (Hb _ _ stn) csumC cdiff_pr1 - ? eq1 //.
Qed.


  
End IncFun.

Module Rat.
Definition Qpair k n := 
  BQ_of_pair (BZ_of_nat k) (BZ_of_nat (\2c ^c n)).

Lemma zpow2_pos n: natp n -> inc (BZ_of_nat (\2c ^c n)) BZps.
Proof.
move => nN; apply/BZps_iP; split.
   apply:(BZ_of_natp_i (NS_pow NS2 nN)).
move/(f_equal BZ_val); rewrite BZ0_val  BZ_of_nat_val; apply: cpow_nz.
exact: card2_nz.
Qed.

Lemma Qpair_q k n: natp k ->  natp n -> ratp (Qpair k n).
Proof.
move => kN nN; exact: (BQ_of_pair_prop4 (BZ_of_nat_i kN) (zpow2_pos nN)).
Qed.

Lemma Qpair_eq k n m: natp k -> natp n -> natp m ->
  Qpair k n = Qpair (k *c \2c ^c m) (m +c n).
Proof.
move => kN nN mN.
move: (NS_pow NS2 mN) => fN; move: (NS_prod   kN fN) => pN.
move: (zpow2_pos nN) (zpow2_pos (NS_sum mN nN)) => pa pb. 
apply/ (BQ_of_pair_prop5 (BZ_of_nat_i kN) pa (BZ_of_nat_i pN) pb).
rewrite (BZprod_cN kN (NS_pow NS2 (NS_sum mN nN))).
rewrite (BZprod_cN (NS_pow NS2 nN) pN); apply: f_equal.
by rewrite (cprodC (\2c ^c n)) - cprodA - cpow_sum2.
Qed.

Lemma Qpair_le0P a b c d:
  natp a -> natp b -> natp c -> natp d ->
  let f:= fun k n =>  k *c (\2c ^c n) in
   (Qpair a b) <=q (Qpair c d) <-> (f a d) <=c (f c b).
Proof.
move => aN bN cN dN /=.
apply: (iff_trans (BQ_le_pair (BZ_of_nat_i aN) 
    (zpow2_pos bN)(BZ_of_nat_i cN) (zpow2_pos dN))).
move: (NS_pow NS2 dN) (NS_pow NS2 bN) => p1N p2N.
rewrite (BZprod_cN aN p1N) (BZprod_cN p2N cN) (cprodC c).
apply:iff_sym. apply: (zle_cN (NS_prod aN p1N) (NS_prod p2N cN)).
Qed.

Lemma Qpair_leP k k' n: natp k -> natp k' -> natp n -> 
 (k <=c k' <-> (Qpair k n) <=q (Qpair k' n)).
Proof.
move=>  kN k'N nN.
symmetry;apply: (iff_trans (Qpair_le0P kN nN k'N nN)).
split; first by apply:(cprod_le2r (NS_pow NS2 nN) kN k'N (@cpow2_nz n)). 
apply: cprod_Mleeq.
Qed.


Definition Qpairi k n :=
   interval_cc BQ_order (Qpair k n) (Qpair (csucc k) n). 
Definition Qpairis := 
  fun_image (Nat \times Nat) (fun z => Qpairi (P z) (Q z)).
Definition Qpairi_o := opp_order (sub_order Qpairis). 

Lemma Qpairis_prP x: 
  inc x Qpairis <->
  exists k n, [/\ natp k, natp n & x =  Qpairi k n].
Proof.
split.
  move /funI_P => [z /setX_P [pe Pqz Qz] xe].
  by exists (P z); exists (Q z).
move=> [k [n [kB nB xe]]]; apply /funI_P; exists (J k n); aww.
Qed.


Lemma Qpairio_osr: order_on Qpairi_o  Qpairis.
Proof. 
move:(sub_osr Qpairis) => [pa pb].
move: (opp_osr pa) => [pc pd]. 
rewrite /Qpairi_o /order_on; split => //; ue.
Qed.

Lemma Qpairio_gleP x y: 
   gle Qpairi_o x y <-> [/\ inc x  Qpairis, inc y  Qpairis & sub y x].
Proof. 
apply: (iff_trans (opp_gleP _ _ _)).
split; first by move /sub_gleP => [p1 p2 p3].
by move => [pa pb pc]; apply /sub_gleP.
Qed.

Lemma Qpairis_pr1P n k x: inc x (Qpairi k n) 
  <-> (Qpair k n) <=q x /\  x <=q (Qpair (csucc k) n). 
Proof.
split; first by  move => /Zo_hi [/BQle_P ha /BQle_P hb ].
move => [/BQle_P pa /BQle_P pb]; apply: Zo_i => //; order_tac.
Qed.

Lemma Qpairis_pr2 k n: natp k -> natp n ->
  (inc (Qpair k n)  (Qpairi k n) /\ inc  (Qpair (csucc k) n) (Qpairi k n)).
Proof.
move=> kN xN; move: (NS_succ kN) => skN.
have p5:(Qpair k n) <=q (Qpair (csucc k) n) by apply /Qpair_leP; fprops.
move:(p5) =>[gha hb _].
have p3:(Qpair k n) <=q (Qpair k n) by apply: qleR. 
have p4:(Qpair (csucc k) n) <=q (Qpair (csucc k) n) by apply: qleR. 
by split; apply/Qpairis_pr1P.
Qed.

Lemma Qpairio_gle1P k n l m: natp k -> natp n -> natp l -> natp m  -> 
  let f:= fun k n => (k *c (\2c ^c n)) in
  gle Qpairi_o (Qpairi k n) (Qpairi l m) <->
  ((f k m) <=c  (f l n)  /\ (f (csucc l) n) <=c (f (csucc k) m)).  
Proof.
move=> kN nN lN mN f.
move: (Qpairis_pr2 lN mN) => [p4 p5].
split.
move /Qpairio_gleP => [p1 p2 p3]. 
   move: (p3 _ p4) => /Qpairis_pr1P [q1 q2].
   move: (p3 _ p5) => /Qpairis_pr1P [q3 q4].
   split. 
     by apply /(Qpair_le0P kN nN lN mN).
     by apply /(Qpair_le0P (NS_succ lN) mN (NS_succ kN) nN).
move => [] /(Qpair_le0P kN nN lN mN) pa 
   /(Qpair_le0P (NS_succ lN) mN (NS_succ kN) nN) pb.
apply /Qpairio_gleP;split => //.
    by apply /Qpairis_prP;exists k, n.
  by apply /Qpairis_prP;exists l, m.
move=> t /Qpairis_pr1P [q3 q4]; move:(qleT pa q3) (qleT q4 pb) => r1 r2.
apply /Qpairis_pr1P;split => //.
Qed.

Lemma Qpairio_gle2P k n l m: natp k -> natp n ->  natp l -> natp m -> 
  let f:= fun k n => (k *c (\2c ^c n)) in
  gle Qpairi_o (Qpairi k n) (Qpairi l m) <->
  (exists p, [/\ natp p, m = n +c p,
    (f k p) <=c l & (csucc l) <=c (f (csucc k) p)]).
Proof.
move=> kN nN lN mN f.
have n2N: natp (\2c ^c n) by fprops.
split; last first.
  move=> [p [pN eq le1 le2]]. 
  apply /(Qpairio_gle1P kN nN lN mN); rewrite eq cpow_sum2; split.
      rewrite cprodA  (cprodC k _) - cprodA cprodC.
    apply: cprod_Mlele; fprops. 
  rewrite cprodA (cprodC (csucc k) _) - cprodA cprodC.
  apply: cprod_Mlele; fprops. 
move/ (Qpairio_gle1P kN nN lN mN). 
rewrite (cprodC (csucc l) _)(cprodC (csucc k) _).
move=> [r1 r02]; move: (r02).
have m2N: natp (\2c ^c m) by fprops.
rewrite cprod_nS // cprod_nS //.
rewrite (cprodC  _ l)(cprodC _ k)  -/(f k m)  -/(f l n) => r2.
have r3:(\2c ^c n) <=c (\2c ^c n) by fprops.
move: (csum_Mlele r1 r3) => r4.
move: (cleT r4 r2) => r5.
have fN: natp (f k m) by rewrite /f; fprops.
move: (csum_le2l fN n2N m2N r5) => aux.
have nm: n <=c m.
  case: (cleT_el (CS_nat nN) (CS_nat mN)) => // nm.
  case: (cleNgt aux (cpow_Meqlt NS2 nN nm clt_12)).
move: (cdiff_pr nm); set p := (m -c n) => cp.
have pN: natp p by apply: NS_diff.
move: r1 r02; rewrite - cp cpow_sum2.
set ptn:=  (\2c ^c n).
rewrite cprodA (cprodC k _) - cprodA  -/(f k p)(cprodC _ ptn).
rewrite - cprodA (cprodC _ (csucc k)) -/(f (csucc k) p) => r1 r6.
have knz: ptn <> \0c by apply: cpow2_nz.
have fkpN: natp (f k p) by rewrite /f; fprops.
have fkspN: natp (f (csucc k) p) by rewrite /f; fprops.
exists p; split => //.
  apply: (cprod_le2l n2N fkpN lN knz r1).
apply: (cprod_le2l n2N (NS_succ lN) fkspN  knz r6).
Qed.

Lemma Qpairio_eq k n l m: 
  natp k -> natp n -> natp l -> natp m  -> 
   (Qpairi k n) = (Qpairi l m) -> (k = l /\ n = m).
Proof.
move=>  kN nN lN mN eq1.
move: Qpairio_osr => [qo qs].
have mqs: inc (Qpairi k n) (substrate Qpairi_o).
  rewrite qs; apply /Qpairis_prP; exists k; exists n;split => //.
have aux: gle Qpairi_o (Qpairi k n) (Qpairi k n) by order_tac.
move: (aux); rewrite {2} eq1 => /(Qpairio_gle2P kN nN lN mN).
   move => [p [pN np le1 le2]].
move: aux; rewrite {1} eq1 => /(Qpairio_gle2P lN mN kN nN).
  move => [q [qN nq le3 le4]].
move: (Nsum_M0le p nN)(Nsum_M0le q mN).
rewrite -np -nq => le5 le6.
have nm: n = m by exact: cleA. 
have r1: n +c \0c = n +c p by rewrite csum0r; [rewrite -np nm | fprops].
have r2: m +c \0c = m +c q by rewrite csum0r; [rewrite -nq nm | fprops].
move: le1; rewrite -(csum_eq2l nN NS0 pN r1).
rewrite cpowx0 cprod1r; fprops => kl.
move: le3; rewrite -(csum_eq2l mN NS0 qN r2).
rewrite cpowx0 cprod1r; fprops => lk.
split => //; exact: cleA.
Qed.

(** This set has no maximal element *)

Lemma Exercise1_24b x:
  inc x (substrate Qpairi_o) -> ~ (maximal Qpairi_o x).
Proof.
rewrite  (proj2 Qpairio_osr) => /Qpairis_prP  [k [n [kN nN xv]]].
set y :=  Qpairi (k *c \2c) (csucc n).
move: NS2 NS1 => b2 b1.
have aux: gle Qpairi_o x y.
  have p1: natp (k *c \2c) by fprops.
  have p2: natp (csucc n) by fprops.
  have p3: cardinalp k by fprops.
  have p4: cardinalp \2c by fprops.
  have p5: cardinalp (k *c \2c) by fprops.
  rewrite xv /y; apply  /Qpairio_gle2P => //.
  exists \1c. 
  rewrite (cpowx1 p4) - csucc_pr4 //; fprops; split;fprops.
  rewrite !csucc_pr4 // cprodDl. 
  have ->: \1c *c \2c = \1c +c \1c
    by rewrite cprod1l//  csum_11.
  rewrite csumA.
  apply: Nsum_M0le; fprops.
move=> [_ h]; move: (h _ aux).
have k2N: natp (k *c \2c) by fprops. 
rewrite xv /y=> xy. 
move: (Qpairio_eq k2N (NS_succ nN) kN nN xy) => [_ sn].
by move: nN => /NatP /finite_cP [_] [].
Qed.

Lemma Qpairio_gle3  k n l m z:
  natp k -> natp n -> natp l -> natp m -> 
  n <=c m  ->
  gle Qpairi_o (Qpairi k n) z -> gle Qpairi_o(Qpairi l m) z ->
  gle Qpairi_o (Qpairi k n) (Qpairi l m).
Proof.
move=> kN nN lN mN nm le1 le2.
have: inc z (substrate  Qpairi_o) by order_tac.
rewrite (proj2 Qpairio_osr) => / Qpairis_prP [i [s [iN sN zv]]].
move: le1 le2; rewrite zv 
  => /(Qpairio_gle2P kN nN iN sN)  [p [pN s1 le1 le2]]
   /(Qpairio_gle2P lN mN iN sN) [q [qN s2 le3 le4]].
move: (cdiff_pr nm); set t:=(m -c n) => tp.
have tN: natp t   by apply: NS_diff.
have ptq: p = q +c t.
   apply: (@csum_eq2l n) => //; fprops.
   by rewrite (csumC q t) csumA tp - s1.
have ptq1: p = t +c q by rewrite csumC.
move: le1 le2; rewrite ptq1 cpow_sum2 cprodA cprodA => le1 le2.
apply /(Qpairio_gle2P kN nN lN mN); exists t.
move: le1 le2 le3 le4.
set kt :=  (k *c (\2c ^c t)).
set kpt :=  ((csucc k) *c  (\2c ^c t)).
set q2:= (\2c ^c q).
move: NS2 => bs2.
have kpN: natp kt by rewrite /kt; fprops.
have kptN: natp kpt by rewrite /kpt; fprops.
have q2N: natp q2 by rewrite / q2; fprops.
have kptqN: natp (kpt *c q2) by fprops.
have lpqN: natp ((csucc l) *c q2) by fprops.
move => le1 /(cleSltP iN) le2 le3 /(cleSltP iN) le4.
move: (cle_ltT le1 le4) (cle_ltT le3 le2).
have knz: q2 <> \0c.
  by apply: cpow_nz; fprops.
rewrite !(cprodC _ q2) => le5 le6;split => //.
  apply /cltSleP=>//;apply: (@cprod_lt2l q2) => //; fprops.
apply /(cleSltP lN).
apply: (@cprod_lt2l q2) => //. 
Qed.


Lemma Qpairio_gle4 x y:
   inc x (substrate Qpairi_o) -> inc y (substrate Qpairi_o) ->
   [\/ gle Qpairi_o x y,
   gle Qpairi_o y x |
   (forall z : Set, gle Qpairi_o x z -> gle Qpairi_o y z -> False)]. 
Proof.
move=> xs ys.
case: (p_or_not_p (gle Qpairi_o x y)) => h1; first by constructor 1.
case: (p_or_not_p (gle Qpairi_o y x)) => h2; first by constructor 2.
move: (xs) (ys); rewrite (proj2 Qpairio_osr)  => /Qpairis_prP.
move=> [k [n [kN nN xv]]] /Qpairis_prP [l [m [lN mN yv]]].
constructor 3; rewrite xv yv; move=> z le1 le2. 
case: (cleT_ee  (CS_nat nN) (CS_nat mN)) => // nm.
  case: h1; rewrite xv yv; apply: (Qpairio_gle3 kN nN lN mN nm le1 le2).
case: h2; rewrite xv yv; apply: (Qpairio_gle3 lN mN kN nN nm le2 le1).
Qed.

(** The set is antiditected thus branched *)

Lemma Exercise1_24c: anti_directed Qpairi_o.
Proof.
move: Qpairio_osr => [h0 sr].
apply/(Exercise1_23hP h0); split => //.
  move=> x y [lexy nxy].
  have xs: inc x (substrate Qpairi_o) by order_tac.
  have ys: inc y (substrate Qpairi_o) by order_tac.
  move: (xs) (ys); rewrite sr  => /Qpairis_prP
     [k [n [kN nN xv]]] /Qpairis_prP [l [m [lN mN yv]]].
  move: lexy; rewrite xv yv=> /(Qpairio_gle2P kN nN lN mN) [p [pN nm le1 le2]].
  have skN:= NS_succ kN. 
  case: (equal_or_not p \0c) => pz.
    move: le1 le2; rewrite pz cpowx0 !cprod1r; fprops => le1.
    move /(cleSSP (CS_nat lN) (CS_nat kN)) => le2.
    by case: nxy; rewrite xv yv (cleA le1 le2) nm pz Nsum0r.
  have nmn: m <> n.
    dneg mn. apply: (@csum_eq2l n) => //; fprops.
    by rewrite -nm mn Nsum0r.
  set q2:= (\2c ^c p) in le1 le2.
  set kq2 := (k *c q2) in le1.
  set l':= Yo (l = kq2) (csucc l) kq2.
  have l'N: natp l' by move: NS2=> b2; rewrite /l'/kq2/ q2; Ytac aux; fprops.
  have ll': l <> l'.
    rewrite /l'; Ytac aux =>//; exact: (proj2(cltS lN)).
  set z :=  Qpairi l' m.
  exists z => //.
    split; last first.
     rewrite /z => eq; move: (Qpairio_eq kN nN l'N mN eq) => [_ nm'].
     by case: nmn.
    apply /Qpairio_gle2P => //; exists p; rewrite -/ q2 -/kq2.
    have lsl: l <=c (csucc l) by apply: cleS.
    have p1:= cleT le1 lsl.
    have p2:= cleR (proj31 p1).
    have q2N: natp q2 by rewrite / q2; fprops.
    have kq2N: natp kq2 by rewrite /kq2; fprops.
    have skq2: natp ((csucc k) *c q2) by fprops.
    have knz: q2 <> \0c by apply: cpow2_nz.
    have le3: (csucc kq2) <=c  ((csucc k) *c q2).
      apply /cleSltP => //; split; first exact : (cleT p1 le2).
      rewrite cprodC cprod_nS // cprodC -/kq2.
      dneg aux1; apply: (@csum_eq2l kq2) => //; fprops. 
      by rewrite -aux1 Nsum0r.
    split => //; first by  rewrite /l'; Ytac aux => //.
    rewrite /l'; Ytac aux => //.
    have slN: natp (csucc l) by fprops.
    have ckq2: cardinalp kq2 by fprops.
    apply /(cleSltP slN) => //; split => //.
    rewrite aux csucc_pr4// cprodC cprod_nS // cprodC -/kq2.
    move=> aux2.
    move: (csum_eq2l kq2N NS1 q2N aux2) => q21.
    move: NS1 (cpow_Mle1 CS2 pz) => oN.
     by rewrite -/ q2 - q21 - succ_one;move /(cleSltP oN) => [_ ];case.
  move=> t; rewrite /z=> le1a le2a.
  have mm: m <=c m by fprops.
  move: (Qpairio_gle3 lN mN l'N mN mm le1a le2a).
  move /(Qpairio_gle1P lN mN l'N mN).
  set m2:= (\2c ^c m).
  have m2N: natp m2 by rewrite /m2; fprops.
  have knz: m2 <> \0c by apply: cpow2_nz.
  rewrite !(cprodC _ m2); move => [le3 le4].
  have le5: l <=c l'. 
    apply: (@cprod_le2l  m2) => //. 
  have : (csucc l') <=c (csucc l). 
    apply: (@cprod_le2l  m2) => //; fprops.
  have cl: cardinalp l' by fprops.
  by move /(cleSSP cl (CS_nat lN)) => le6;case: ll'; apply:cleA.
move=> x y xs ys.
case: ( Qpairio_gle4 xs ys);first by constructor 1.
  by constructor 2.
by move=> h; constructor 3; exists x  => //; order_tac.
Qed.

Lemma Exercise1_24d: branched Qpairi_o.
Proof.
apply: (Exercise1_24a (proj1 Qpairio_osr) Exercise1_24c Exercise1_24b).
Qed.


Lemma Exercise1_24f: forall r' X, let r := Qpairi_o in
  let R := (order_product2 r r') in 
  worder r' -> sub X (substrate R) -> cofinal R X  ->
       anti_directed (induced_order R X) -> False.
Proof.
move => r' X r R wor' Xsr cfs anX.
have or': order r' by move: wor' => [ok _].
move:  Qpairio_osr => [or sr].
have oR: order R by apply: order_product2_or => //.
move: (order_product2_sr or or') => sp.
set R' := (induced_order R X).
rewrite -/R' -/r in sp.
set S:= (substrate r) \times (substrate r').
have srR': substrate R' = X by apply: iorder_sr.
have oi: order R' by rewrite /R'; apply: (proj1 (iorder_osr oR _)).
set Aux:= fun x y => 
  forall z, gle R' x z -> gle R' y z -> False.
move: anX => /(Exercise1_23hP oi) [p01 p02].
have p1: forall x y, glt R' x y -> exists2 z : Set, glt R' x z & Aux y z. 
  by rewrite /Aux/R'.
have p2: forall x y : Set, inc x (substrate R') -> inc y (substrate R') ->
   [\/ gle R' x y, gle R' y x, (exists2 x' ,  gle R' x x' & Aux x' y)
        | (exists2 y' : Set,  gle R' y y'& Aux x y')].
  by rewrite /Aux.
clear p01 p02.
have aux: forall x y,inc x (substrate R') -> inc y (substrate R') ->
    gle r (P x) (P y) -> ~ (Aux x y).
  move=> x y xsr ysr pxy aux.
  rewrite srR' in p2 xsr ysr.
  have xs1: inc x S by rewrite /S - sp; apply: Xsr. 
  have ys1: inc y S by rewrite /S - sp; apply: Xsr. 
  move: (xs1) (ys1) =>  /setX_P  [px Px Qx] /setX_P [py Py Qy].
  move: (worder_total wor') =>  [_ tor].
  case: (tor _ _ Qx Qy) => le2.
    case: (aux y); first by apply /iorder_gle0P=> //; apply /order_product2_P.
    order_tac; ue.
  set t := J (P y) (Q x).
  have ts: inc t S by rewrite /t;apply /setXp_P;split;fprops.
  have Rxt: (gle R x t). 
    apply /order_product2_P.
    by split=> //; split=> //; rewrite /t;aww; order_tac.
  have Ryt: (gle R y t). 
    apply /order_product2_P.
    by split=> //; split => //;  rewrite /t;aw; trivial;order_tac.
  have trs: inc t (substrate R) by order_tac.
  move: cfs => [_ hh]; move: (hh _ trs) => [w wX tw].
  case: (aux w);   apply /iorder_gle0P => //; order_tac.
have aux2: forall x y, inc  x (substrate R') -> inc y (substrate R') ->
    (Aux x y <-> (~ gle r (P x) (P y)  /\ ~ gle r (P y) (P x))).
  move=> x y xsr ysr.
  case: (p_or_not_p (gle r (P x) (P y))) => r1.
    move: (aux _ _ xsr ysr r1) => r3.
    split => // [] [u1 u2] //.
  case: (p_or_not_p (gle r (P y) (P x))) => r2.
    move: (aux _ _ ysr xsr r2) => r3.
    split; last by move=> [u1 u2].
    move=> aux3; case: r3 => z z1 z2; case: (aux3 z) => //.
  split => _; first by split => //.
  have xs1: inc x S by rewrite /S - sp; apply: Xsr; ue.
  have ys1: inc y S by rewrite /S - sp; apply: Xsr; ue.
  move: (xs1) (ys1) => /setX_P [px Px Qx]  /setX_P [py Py Qy].
  case: (Qpairio_gle4 Px Py); first by done.
     by done.
  move => raux z z1 z2.
  move: (iorder_gle1 z1) (iorder_gle1 z2) => /order_product2_P
      [_ _ [r3 _]] /order_product2_P [_ _ [r4 _]].
  case: (raux _ r3 r4).
Abort.



End Rat.
Module Zermelo.


(** Direct proof of the transfinite principle  *)

Lemma transfinite_principle_bis r (p:property):
  worder r ->  
  (forall x, inc x (substrate r) ->
    (forall y, glt r y x -> p y) -> p x) -> 
  forall x, inc x (substrate r) -> p x.
Proof. 
move => [or wor] hyp x xsr; ex_middle npx.
set (X:=Zo (substrate r) (fun x => ~ p x)). 
have neX: (nonempty X) by exists x; apply: Zo_i.
have Xsr: sub X (substrate r) by apply: Zo_S.  
move:(wor _ Xsr neX)=> [y []]; rewrite iorder_sr // => /Zo_P [ysr npy] yle.
case: npy; apply: hyp =>//.
move=> t ty; ex_middle npt.
have tsr: inc t (substrate r) by order_tac.
move: (iorder_gle1 (yle _ (Zo_i tsr npt))) => nty; order_tac.
Qed.

Definition segment_rp r s:=
  sub s (substrate r) /\ (forall x y, inc x s -> gle r x y -> inc y s).

Lemma segment_rpC r x : order r -> sub x (substrate r) ->  
    (segmentp r x <-> segment_rp r (substrate r -s x)).
Proof.
move => or xsr; split => [][sa sb].
  split; first by apply: sub_setC.
  move => a b /setC_P [asr nax] lab; apply:setC_i; first by order_tac.
  dneg bx; apply: (sb _ _ bx lab).
split => // a b ax lba; ex_middle bnx.
have iby: inc b (substrate r -s x) by apply/setC_P; split => //; order_tac.
by case/setC_P: (sb _ _ iby lba). 
Qed.

Lemma segment_rpC' r x : order r -> sub x (substrate r) ->  
    (segment_rp r x <-> segmentp r (substrate r -s x)).
Proof.
move => or xsr; apply:iff_sym.
rewrite - {2}(setC_K xsr). apply:(segment_rpC or); apply:(sub_setC). 
Qed.

Lemma segment_rC r x: total_order r -> inc x (substrate r) ->
  (segment_r r x) = substrate r -s (segment r x).
Proof. 
move => [or tor] xsr; set_extens y.
  move => /segment_rP ha; apply /setC_P; split; first by order_tac.
  move/segmentP => hb; order_tac. 
move => /setC_P [ysr /segmentP ha]; apply/segment_rP.
case: (equal_or_not y x) => exy; first by rewrite exy; order_tac.
by case: (tor _ _ xsr ysr) => // hb; case: ha.
Qed.

Lemma segment_rC' r x: total_order r -> inc x (substrate r) ->
  (segment r x) = substrate r -s (segment_r r x).
Proof.
by move=> sa sb; rewrite (segment_rC sa sb) setC_K //; apply: sub_segment.
Qed.

Lemma segment_r_p0 r: segment_rp r emptyset. 
Proof. by split; fprops => cx y /in_set0. Qed.

Lemma segment_r_p1 r x: order r -> inc x (substrate r) -> 
  segment_rp r (segment_r r x). 
Proof.
move => or xsr.
split; first by move => y /segment_rP le; order_tac.
move => a b /segment_rP le1 le2; apply/segment_rP; order_tac.
Qed.

Lemma segment_rp_p2 r z:
  order r -> inc z (substrate r) -> segment_rp r (segment_r r z -s1 z).
Proof.
move => or zr.
split; first by move => t /setC1_P [/segment_rP le _]; order_tac.
move => x y /setC1_P [/segment_rP le1 ne1] le2; apply/setC1_P; split.
  apply/segment_rP; order_tac.
by dneg xx; rewrite xx in le2; order_tac.
Qed.

Lemma segment_rp_p3 r s: order r ->  
   (alls s (segment_rp r)) -> segment_rp r (intersection s).
Proof. 
move => or al.
case: (emptyset_dichot s) => nes. 
  rewrite nes setI_0; apply: segment_r_p0.
move:(nes) => [k ks].
split.
  move => t ti; exact: (proj1 (al _ ks) _ (setI_hi ti ks)).
move => x y xI lxy; apply: (setI_i nes)  => a ias.
move: (al _ ias) => [_ sy]; exact :(sy _ _ (setI_hi xI ias) lxy).
Qed.


Lemma segment_r_succ_or_limit r x: worder r -> inc x (substrate r) ->
  [\/ (segment_r r x = substrate r),
  (exists2 z, inc z (segment r x) & segment_r r x = segment_r r z -s1 z) |
  (segment_r r x) = intersection (fun_image (segment r x) (segment_r r)) ].
Proof.
move => wor xsr.
have tor:= (worder_total wor).
have or := proj1 wor.
set T := segment r x.
case: (emptyset_dichot T) => te.
  by move: (segment_rC tor xsr); rewrite -/T te setC_0 => h; constructor 1.
have TE: sub T (substrate r) by apply: sub_segment.
have Tb: bounded_above r T by exists x; split => // y /segmentP [].
move: (worder_hassup wor TE Tb) => [z /(lubP or TE) [[za zb] zc]].
case: (inc_or_not z T) => zT.
  constructor 2; ex_tac.
  have ltx: glt r z x by apply /segmentP.
  set_extens u.
     move /segment_rP => l1.
     have [l2 /nesym n2]: glt r z u by order_tac.
     by apply/setC1_P; split => //;apply /segment_rP.
  move => /setC1_P [/segment_rP qa qb]; apply /segment_rP.
  have uE: inc u (substrate r) by order_tac.
  case: (equal_or_not u x) => eq; first by rewrite eq; order_tac. 
  case: (proj2 tor _ _ xsr uE) => // le1.
  move /segmentP: (conj le1 eq) => /zb  le2; case: qb; order_tac.
constructor 3.
have nf: nonempty (fun_image T (segment_r r)) by apply:funI_setne.
set_extens t.
  move /segment_rP => h; apply /(setI_P nf) => i /funI_P [u /segmentP zu ->].
  move: zu => [zu _];apply /segment_rP; order_tac.
move => /(setI_P nf) h; apply /segment_rP.
have hh: forall q, inc q T -> gle r q t.
  move => q qt;apply /segment_rP; apply: h; apply/funI_P; ex_tac.
have tE: inc t (substrate r) by move: te => [u /hh ut];  order_tac. 
have zt : gle r z t by apply:zc; split => //; apply: hh.
case: (equal_or_not z x) => eq; first by rewrite - eq.
have zE: inc z (substrate r) by order_tac.
case: (proj2 tor _ _ xsr zE) => // le1;first order_tac. 
by case: zT; apply /segmentP.
Qed.

Definition segment_rs r:= (fun_image (substrate r) (segment_r r) +s1 emptyset).

Lemma segment_rs_P r x: 
  (inc x (segment_rs r) <-> 
     x = emptyset \/ (exists2 y, inc y (substrate r) & x = segment_r r y)).
Proof.
split; first by case /setU1_P; [ by move/funI_P; right | by left].
by move => ww; apply/setU1_P; case:ww; [right| left; apply/funI_P].
Qed.

Lemma segment_rs_p1 r: worder r ->
  forall x, inc x (segment_rs r) <-> segment_rp r x.
Proof.
move => wor x; apply:(iff_trans (segment_rs_P r x)); split.
  case; first by  move => ->;  apply:segment_r_p0.
  move => [y ysr ->]; exact:(segment_r_p1 (proj1 wor) ysr).
move => ss.
move /(segment_rpC' (proj1 wor) (proj1 ss)): (ss) => ss'.
case:(well_ordered_segment wor ss').
  by move => sa; left; rewrite -(setC_K (proj1 ss)) sa setC_v.
move => [y ysr yv]; right; exists y => //.
by rewrite (segment_rC (worder_total wor) ysr) - yv (setC_K (proj1 ss)).
Qed.


Lemma Zermelo_omega_chain r (E := substrate r): Zermelo_like r -> 
  Zermelo_chain E (segment_rs r).
Proof.
move => [ha hb]; move: (ha) => [or wor].
have ra: sub (segment_rs r) (\Po E).
  by move => t /(segment_rs_p1 ha) [/setP_P ts _].
have rb: inc (substrate r) (segment_rs r).
  apply/(segment_rs_p1 ha); split => // x y xsr le; order_tac.
have rc: forall A, inc A (segment_rs r)  -> inc (A -s1 rep A) (segment_rs r).
  move => A /segment_rs_P; case.
    by move => ->; apply /setU1_P; right;apply/set0_P => t /setC1_P [/in_set0].
  move => [z zE ->]; rewrite (hb _ zE). 
  by apply/(segment_rs_p1 ha) /segment_rp_p2.
split => // A Aom neA; apply/(segment_rs_p1 ha). 
by apply:(segment_rp_p3 or) => t /Aom /(segment_rs_p1 ha).
Qed.

Lemma Zermelo_chain_least E F: Zermelo_chain E F -> inc emptyset F.
Proof.
move => [pa pb pc pd].
have nef: nonempty F by exists E; apply: pb.
move: (pd _ (@sub_refl F) nef); set x := intersection F => iF.
case: (emptyset_dichot x); [by move <- | move => xne].
move: (pc _ iF) => siF.
by move: (setI_hi  (rep_i xne) siF) => /setC1_P [].
Qed.

Lemma Zermelo_chain_minimal1 r (E := substrate r):
  Zermelo_like r -> 
  forall F, Zermelo_chain E F -> sub (segment_rs r) F.
Proof.
move => [wor ha] F zl => t /(segment_rs_P).
have eF := (Zermelo_chain_least zl).
case; first by move => ->.
have or := proj1 wor.
move: (zl) => [pa pb pc pd] [k kE ->].
move: k kE. apply:(transfinite_principle_bis wor) => x xsr H.
case: (segment_r_succ_or_limit wor xsr).
- by move ->.
- move => [z /segmentP ltx ->]; move: (pc _ (H _ ltx)); rewrite ha //.
  order_tac.
- move ->; case: (emptyset_dichot (segment r x)) => te.
    by rewrite te funI_set0 setI_0.
  apply:pd; last by apply: funI_setne.
  by move => u /funI_P [z /segmentP /H h ->].
Qed.

Lemma Zermelo_chain_minimal r (E := substrate r):
  Zermelo_like r -> 
  (segment_rs r) = intersection (Zo (\Po (\Po E)) (Zermelo_chain E)).
Proof.
move => h.
set Z := Zo _ _.
have w: forall F, inc F Z <-> Zermelo_chain E F.
  move => f; split;first by move/Zo_hi.
  by move => zc; apply: Zo_i => //; apply /setP_P; move: zc=> [].
have ha: inc (segment_rs r) Z by apply/w/Zermelo_omega_chain.
set_extens t; last by move => ts; exact:(setI_hi ts ha).
move => ts; apply/setI_P; [ex_tac | move => i /w ci].
exact: (Zermelo_chain_minimal1 h ci ts).
Qed.

Lemma Zermelo_unique r r': Zermelo_like r -> Zermelo_like r' ->
   substrate r = substrate r' -> r = r'.
Proof. 
move => ha hb ss.
have ch12: (segment_rs r) =  (segment_rs r'). 
  rewrite (Zermelo_chain_minimal ha).
  by rewrite (Zermelo_chain_minimal hb) ss.
move: ha hb => [wor1 ha] [wor2 hb].
move:(wor1)(wor2) => [or1 _][or2 _].
have pa: forall x, inc x (substrate r) -> segment_r r x = segment_r r' x.
  move => x xsr.
  have: inc (segment_r r x) (segment_rs r'). 
     by rewrite - ch12; apply/setU1_P; left; apply/funI_P; ex_tac.
  case /setU1_P.
    move/funI_P => [z za ea]; rewrite ea.
    by move:(f_equal rep ea); rewrite (ha _ xsr) (hb _ za) => ->.
  by move => h; empty_tac1 x; apply/segment_rP; order_tac.
apply:order_exten => // x y.
case: (inc_or_not x (substrate r)) => xE; last first.
  split => h; case xE; [ | rewrite ss ]; order_tac.
have ssx:=(pa  _ xE).
split => /segment_rP; first by rewrite ssx => /segment_rP.
by rewrite - ssx => /segment_rP.
Qed.

Lemma Zermelo_like_chain_least1 r X:
  Zermelo_like r ->  sub X (substrate r) -> nonempty X ->
  exists!Y, [/\ sub X Y, inc Y (segment_rs r) & inc (rep Y) X].
Proof.
move => [pa pb] XE neX.
have or: order r by fprops.
apply/unique_existence; split.
  move:(proj2 pa  _ XE neX) => [y []].
  rewrite (iorder_sr or XE)=> yX yP.
  have yE := (XE _ yX). 
  have ha:sub X (segment_r r y). 
     by move => t /yP /iorder_gle1 tX; apply /segment_rP.
  move/(segment_rs_p1 pa): (segment_r_p1 or yE) => hb.
  have hc:inc (rep (segment_r r y)) X by rewrite pb.
  by exists (segment_r r y).
move => Y1 Y2 [qa qb qc] [qd qe qf].
have [x0 x0X] := neX.
case/segment_rs_P: qb; last move => [y1 y1sr Y1v].
   by move => ye; move:(qa _ x0X); rewrite ye => /in_set0.
case /segment_rs_P:qe; last move =>  [y2 y2sr Y2v].
   by move => ye; move:(qd _ x0X); rewrite ye => /in_set0.
move: qc qf qa qd; rewrite Y1v Y2v pb // pb // => qc qf y1X y2X.
move:(y2X _ qc); move/segment_rP => sa.
move:(y1X _ qf); move/segment_rP => sb.
f_equal; order_tac.
Qed.

(* bof 
Lemma Zermelo_w  E W: sub W (powerset E) -> (inc emptyset W) ->
  (forall X,  sub X E -> nonempty X ->
  exists!Y, (sub X Y /\ inc Y W /\ inc (rep Y) X)) ->
  Zermelo_chain E W.
Proof.
move => wp eW H.
have EW: inc E W. 
  case: (emptyset_dichot E) => neE; first by rewrite neE.
   move: (H E (@sub_refl E) neE) => [x [ [pa [pb _]] _]].
   move: (wp _ pb) => /setP_P xE.
   by rewrite(extensionality pa xE).
have Ha: forall A B, inc B W -> sub A B -> inc (rep B) A -> inc A W -> A = B.
  move => A B BW saB rBA AW.
  have sae: sub A E by move/setP_P:(wp _ BW); apply: (sub_trans).
  have neA: nonempty A by exists (rep B).
  move:(rep_i neA) (@sub_refl A) => raa saa.
  by move: (H A sae neA) => /unique_existence [_]; apply.
Abort.
*)

End Zermelo.

(** ** The von Neuman ordinals *)
Module VonNeumann. 


(* Definition of von Neumann of an ordinal *)
Lemma von_neumann_ordinal E:
  ordinalp E <->    
    (worder (ordinal_o E) /\
    (forall x, inc x E -> segment (ordinal_o E) x = x)).
Proof.
split.
   move => oE; split; first by apply: (ordinal_o_wor oE).
   by move => x xE;apply:ordinal_segment.
move => [sa sb].
have Ha y x: inc x E -> inc y x -> ssub y x.
  by move => xE; rewrite -{1} (sb _ xE); move/segmentP => [/ordo_leP []]. 
have tE: transitive_set E.
  by move => x xE y; rewrite - (sb _ xE); move/segmentP => [/ordo_leP []].
have aE: asymmetric_set E. 
  move => y z yE zE /(Ha _ _ zE) [pa pb] /(Ha _ _ yE) [pc _].
  by case: pb; apply:extensionality.
suff: (ordinal_o E) = (ordinal_oa E).
  by move => h; rewrite h in sa;apply/ordinal_pr1.
have g1: sgraph (ordinal_o E) by move: (ordinal_o_or E) => [].
have g2: sgraph (ordinal_oa E) by move => t /Zo_S /setX_P [].
apply:sgraph_exten => // u v. rewrite /ordinal_oa.
split => /graph_on_P1 [uE vE h]; apply /graph_on_P1; split => //.
  case: (equal_or_not u v) => euv; [by right | left].
  by rewrite -(sb _ vE); apply/segmentP; split => //; apply/ordo_leP.
case: h; [ move => ub; exact (proj1(Ha _ _ vE ub)) |  by move ->].
Qed.

(** A [numeration] is a functional graph [f] such that [f(x)] 
is the set of all [f(y)] 
where [y<x] for [r]. A set is [numerable] if well-ordered and there is a 
[numeration]. 
*)


Definition numeration r f:=
  [/\ fgraph f, domain f = substrate r &
  forall x, inc x (domain f) ->  Vg f x = direct_image f (segment r x)].
Definition  numerable r :=
   worder r /\ exists f, numeration r f.

(** Each set has at most one numeration *)
Lemma direct_image_exten f f' a:
  fgraph f -> fgraph f' -> (forall x, inc x a -> Vg f x = Vg f' x) ->
  sub a (domain f) -> sub a (domain f') ->
  direct_image f a = direct_image f' a.
Proof.
move=> fgf fgf' sVVg adf adf'.
set_extens x; move /dirim_P => [u us Jg]; apply /dirim_P; ex_tac.
  move: (pr2_V fgf Jg); aw; move=> ->; rewrite (sVVg _  us). 
  by apply: fdomain_pr1 =>//;  apply: adf'. 
move: (pr2_V fgf' Jg); aw; move=> ->; rewrite -(sVVg _  us). 
by apply: fdomain_pr1 =>//;  apply: adf. 
Qed.

Lemma numeration_unique r f f':
  worder r -> numeration r f -> numeration r f' -> f = f'.
Proof.
move=>  [or wor] [fgf df Vf][fgf' df' Vf'].
set A :=Zo (substrate r)(fun x=> Vg f x <> Vg f' x).
case: (emptyset_dichot A)=> neA.
  apply: (fgraph_exten fgf fgf'); rewrite df => // a xdf.
  by ex_middle nVV; empty_tac1 a; apply: Zo_i.
have sAs: sub A (substrate r) by apply: Zo_S.
move: (wor _ sAs neA)=> [y []]; rewrite iorder_sr // => yA leyA.
move: (sAs _ yA)=> ysr.
have srp: forall z, inc z (segment r y) -> Vg f z = Vg f' z.
  move=> z /segmentP zy; ex_middle nVV. 
  have zA: (inc z A) by  apply: Zo_i=>//; order_tac.
  move: (iorder_gle1 (leyA _ zA)) => yz; order_tac.
have nyA: Vg f y = Vg f' y.  
  rewrite df in Vf; rewrite df' in Vf'. 
  rewrite Vf // Vf' //.
  apply: direct_image_exten =>//.
    rewrite df;  apply: sub_segment.
    rewrite df';  apply: sub_segment.
by move: yA => /Zo_P [_ []]. 
Qed.

(** A numeration of a segment is obtained by restriction *)

Lemma sub_numeration r f x:
  let r' := induced_order r (segment r x) in
  worder r ->  numeration r f -> inc x (substrate r) ->
  numeration r' (restr f (segment r x)).
Proof.
move=> r' wor num xsr.
have sss:= (@sub_segment r x).
have wor':=(induced_wor wor sss).
have [fgf df pf]:= num.
have sr':substrate r' = (segment r x) by rewrite /r' iorder_sr; fprops.
have ssd: sub (segment r x) (domain f) by ue.
have dr:domain (restr f (segment r x)) = substrate r' by aw.
split; aww => a asr.
have sra: (segment r' a = segment r a).
  apply: segment_induced_a =>//; fprops. 
  apply: segment_segment; fprops.
rewrite sra (restr_ev _ asr) pf; last by apply:ssd.
have ssad: sub (segment r a) (domain f) by rewrite df; apply:sub_segment.
have sax: sub (segment r a) (segment r x).
  move=> t; move: asr => /segmentP p1  /segmentP p2. 
  have or: order r by fprops.
  apply /segmentP;order_tac.
apply: direct_image_exten; aww.
by move=> z zs; rewrite restr_ev => //; apply: sax. 
Qed.

(** If all segments are numerable so is the whole set *)

Lemma segments_numerables r:
  let r' := fun x => induced_order r (segment r x) in
  worder r -> (forall x, inc x (substrate r)-> numerable (r' x)) ->
  numerable r.
Proof.
move=> r' wor aln.
set f:= (fun x =>  choose (fun y=> numeration (r' x) y)).
have fp: forall x, inc x (substrate r) -> numeration (r' x) (f x). 
  by move=> x xsr; move: (aln _ xsr)=> [_ c];rewrite /f;apply: choose_pr.  
have or: order r by fprops.
have restrp: forall x y, glt r y x ->
   f y = restr (f x) (substrate (r' y)).
  move=> x y ryx.
  have sss: sub (segment r x) (substrate r) by apply: sub_segment.
  have ssy: sub (segment r y) (substrate r) by apply: sub_segment.
  have p6: worder (r' y) by apply: induced_wor =>//.
  apply: (numeration_unique p6); first by apply:  fp; order_tac.
  have <-: (segment (r' x) y) = substrate (r' y).
     rewrite /r' iorder_sr // segment_induced_a //; last by apply/segmentP.
     by  apply:segment_segment.
  have p1: worder (r' x) by rewrite /r'; apply: induced_wor =>//.
  have p2: numeration (r' x) (f x) by apply: fp; order_tac.
  have p3: inc y (substrate (r' x)) by rewrite /r' iorder_sr //; apply /segmentP.
  move: (sub_numeration p1 p2 p3).
  have -> //: induced_order (r' x) (segment (r' x) y) = r' y.
  rewrite /r' segment_induced // iorder_trans //.
  apply: (segment_monotone or (proj1 ryx)).
have gp: forall x y, glt r y x -> range (f y) = Vg (f x) y. 
  move=> x y yx.
  have xsr: (inc x (substrate r)) by order_tac.
  have ysr: (inc y (substrate r)) by order_tac.
  move: (fp _ xsr) => [fg df vf]. 
  move: df; rewrite /r' iorder_sr // => df; last by apply: sub_segment.
  have ysrx: (inc y (segment r x)) by  apply /segmentP.
  rewrite df in vf; rewrite (vf _ ysrx)  (restrp _ _ yx).
  have ->: (segment (r' x) y) = (substrate (r' y)).
    rewrite /r' iorder_sr //;[ by rewrite segment_induced | apply: sub_segment].
  have gr: sgraph (restr (f x) (substrate (r' y))) by fprops.
  have fgr: fgraph (restr (f x) (substrate (r' y))) by fprops.
  have hh: sub (substrate (r' y)) (domain (f x)). 
    rewrite df; rewrite /r' (iorder_sr or (@sub_segment r y)). 
    apply:(segment_monotone or (proj1 yx)).
  set_extens u.
    move /(range_gP fgr); aw; move => [z pa pb]; apply /dirim_P; exists z => //.
    by move: pb; rewrite LgV// => ->; apply:(fdomain_pr1 fg); apply: hh.
  move /dirim_P => [z za zb];apply /(range_gP fgr); exists z; aw; trivial.
  by move: (pr2_V fg zb); rewrite LgV//; aw.
split =>//; exists (Lg (substrate r) (range \o f)).
red; aw; split;fprops.
move=> x xsr; rewrite LgV//.
move: (fp _ xsr) => [ff df vf].
 move: df; rewrite /r' iorder_sr // => df; last by apply: sub_segment.
have gf: sgraph (f x) by fprops.
have p0: sub (segment r x) (substrate r) by apply: sub_segment.
have fgL: fgraph (Lg (substrate r) (range \o f)) by fprops.
set_extens t.
  move=> /(range_gP ff) [z pa pb]; apply /dirim_P; exists z; first ue.
  move: pa; rewrite df => /segmentP h; rewrite pb - (gp _ _ h); apply: Lg_i.
  order_tac.
move /dirim_P => [z xs JL]; move: (p0 _ xs) => zs.
move /segmentP: (xs) => lt1. 
move: (pr2_V fgL JL); aw; rewrite LgV//  => -> /=; rewrite (gp _ _ lt1). 
by apply /(range_gP ff); exists z => //; ue.
Qed. 

(** Any well-ordered is numerable *)

Lemma worder_numerable r:
  worder r ->  numerable r.
Proof.
move=> wor; apply: segments_numerables =>// x xsr.
set r' := fun x => induced_order r (segment r x).
set (A:= Zo (substrate r)(fun z=> ~numerable (r' z))).
case: (p_or_not_p (numerable (induced_order r (segment r x)))) =>// h.
have sA: (sub A (substrate r)) by apply: Zo_S.
have neA: nonempty A  by exists x; apply/Zo_P.
move: (wor)=> [or aux]; move: (aux _ sA neA)=> [y []]. 
rewrite iorder_sr // => ys yp.
have rec: forall z, glt r z y -> numerable (r' z).
  move=>z zy; case: (p_or_not_p (numerable (r' z))) =>// nnz.
  have zA: (inc z A) by rewrite /A; apply: Zo_i=>//; order_tac.
  move: (iorder_gle1 (yp _ zA)) => yz; order_tac.
move: ys => /Zo_P [ys ny]; case: ny.
have sss: sub (segment r y) (substrate r) by apply: sub_segment.
apply: segments_numerables; first by  apply: induced_wor.
rewrite /r' iorder_sr //; move=> z zy.
have rzy: glt r z y by apply /segmentP.
rewrite segment_induced // iorder_trans //;first by apply: rec.
apply: segment_monotone =>//; order_tac.
Qed.

(** The previous result is obvious by [transfinite_defined] *)

Lemma worder_numerable_bis  r:
  worder r -> numeration r (graph (ordinal_iso r)).
Proof. 
move=> wor.
move: (transfinite_defined_pr target wor) => [suf sf vf].
have ff:= proj1 suf. 
hnf; rewrite (domain_fg ff) sf; split; fprops.
move=> x xsr; move: (vf _ xsr); rewrite /Vf; move=> ->; apply:corresp_t.
Qed.


End VonNeumann. 


(** We start with some results that are not in the main files *)

Module Misc2.


(* alternate proof of : there is no set of all cardinals *)
Lemma cantor_bis_alt: non_coll cardinalp.
Proof.
move=> [a ap].
set (s:= union a).  
set (e:= cardinal s).
have cp:= CS_pow \2c e.
case: (cltNge (cantor (CS_cardinal s))).
have /sub_smaller : (sub (\2c ^c e) s) by apply: setU_s1; apply/ ap.
by rewrite (card_card cp).
Qed.


(** Exercise 5.3 of Bourbaki (see part 1)  *)

Lemma exercise5_3 X i j (I:= domain X) (n := cardinal I)
   (ssI := fun k => subsets_with_p_elements k I)
   (uH := fun H => unionb (restr X H))
   (iH := fun H => intersectionb (restr X H))
   (iuH := fun k => intersectionf (ssI k) uH)
   (uiH := fun k => unionf (ssI k) iH):
   fgraph X -> natp n -> natp i -> natp j ->
   (((i = j \/ j <> \0c) -> i +c j <=c csucc n -> sub (iuH i) (uiH j))
   /\ (csucc n <=c i +c j -> (i = j \/ j <=c n) -> sub (uiH i) (iuH j))).
Proof.
move => fgX nN iN jN.
split.
  move => spec le1 t hyp.
  case: (equal_or_not j \0c) => jnz. 
    have i0: i = \0c by case: spec => // ->. 
    move: hyp;  rewrite /iuH /uiH /ssI jnz i0.
    have re: (restr X emptyset) = emptyset.
      apply /set0_P => z /funI_P [a []]; case; case.
    have ->: (subsets_with_p_elements \0c I) = singleton emptyset.
      apply set1_pr.
        by apply/Zo_P; rewrite cardinal_set0;split => //; apply/setP_P; fprops.
      move => z /Zo_P [_]; apply:card_nonempty.
    by rewrite setUf_1 setIf_1 /uH /iH re setUb_0 setIb_0.
  set A := Zo I (fun z => ~ inc t (Vg X z)); set B := I -s A.
  have AI: sub A I by apply : Zo_S.
  move: (cardinal_setC2 AI); rewrite -/n -/B.
  rewrite -(csum2cr A) -(csum2cl A) => eq1.
  have bp: forall z, inc z B -> inc t (Vg X z).
    move => z /setC_P [zI] /Zo_P h; ex_middle tv; case: h;split => //.
  move: (nN);rewrite eq1  => nN'.
  have caN:= (NS_in_suml (CS_cardinal A) nN'). 
  have cbN :=(NS_in_sumr (CS_cardinal B) nN').
  case: (NleT_el jN cbN) => jcb.
    have [C [CB cC]]: exists C, sub C B /\ cardinal C = j.
       move: jcb; rewrite -(card_nat jN) => jcb.
       move: (proj2 (eq_subset_cardP _ _)  (cardinal_le_aux1 jcb)).
       by move =>/set_leP [C c1 /card_eqP/esym c2]; exists C. 
     have CI: sub C I by move => s sC; move:(CB _ sC);move /setC_P => [].
     apply /setUf_P; exists C.
       by apply/ Zo_P; split => //; apply/setP_P.
     apply /setIb_P. 
       apply/domain_set0P;aw; apply /nonemptyP => ce.
       by move: cC; rewrite ce cardinal_set0; apply:nesym.
     by aw;move => l lC; rewrite LgV//; apply: bp; apply: CB.
  have: n <c cardinal A +c j.
    rewrite eq1; rewrite csumC (csumC _ j); apply:csum_Mlteq => //.
  move /(cleSltP nN) => le2.
  move: (cleT le1 le2); rewrite csumC (csumC _ j) => eq2.
  move:(csum_le2l jN iN caN eq2) => icA.
  have [C CB cC]: exists2 C, sub C A & cardinal C = i.
     move: icA; rewrite -(card_nat iN) => icA.
     move: (proj2 (eq_subset_cardP _ _)  (cardinal_le_aux1 icA)).
     by move => /set_leP [C c1 /card_eqP /esym c2]; exists C. 
  have CI: sub C I by move => s sC; move:(CB _ sC); apply: AI.
  have dsi:inc C (ssI i) by apply /Zo_i => //; apply /setP_P.
  move:(setIf_hi hyp dsi)=> /setUb_P [y]; rewrite restr_d.
  by move => yC; rewrite LgV//; move: (CB _ yC) => /Zo_P [].
move => le hij.
move => t /setUf_P [y pa pb]; apply /setIf_P. 
  case: hij => jn; first by rewrite - jn; exists y.
  have kN:= (NS_le_nat jn nN).
  rewrite /ssI; apply /nonemptyP => he.
  move:(esym (card_p_subsets nN kN (refl_equal n))); rewrite he.
  rewrite cardinal_set0; exact: (binom_pr3 nN kN jn).
move => z /Zo_P[/setP_P szi cz].
move /Zo_P:pa => [/setP_P syi cy].
case: (emptyset_dichot (y \cap z)) => di.
  move: (sub_smaller (setU2_12S syi szi)); rewrite (csum2_pr5 di). 
  rewrite -(csum2cr y) cz -(csum2cl y) cy -/n.
  move => le1; case: (cleNgt (cleT le le1) (cltS nN)).
move: di => [l /setI2_P [jz jy]].
apply/setUf_P; exists l;aww.
have jr: inc l (domain (restr X y)) by aw.
move: (setIf_hi pb jr); rewrite !LgV//.
Qed.



Section SuborderFix.

Variables (E: Set)(g: fterm). 
Hypothesis gS: (forall x, sub x E -> sub (g x) E).
Hypothesis gM: (forall x y, sub x y -> sub y E -> sub (g x) (g y)).
Definition suborder_fix x := (sub x E /\ g x = x).
Definition suborder_fix_max := (union (Zo (\Po E)(fun x=> sub x (g x)))).
Definition suborder_fix_min := (intersection (Zo (\Po E)(fun x=> sub (g x) x))).


Lemma suborder_fixU_prop x: suborder_fix x -> sub x suborder_fix_max.
Proof.
move =>[pa pb] t tx; apply/setU_P; exists x => //. 
by apply:Zo_i; [ apply/setP_P | rewrite pb].
Qed.

Lemma suborder_fixI_prop x: suborder_fix x -> sub suborder_fix_min x.
Proof.
move =>[pa pb] t ti.
have xI: inc x (Zo (\Po E) (fun x => sub (g x) x)).
   by apply: Zo_i; [apply/setP_P | rewrite pb].
exact: (setI_hi ti xI).
Qed.

Lemma suborder_fixU: suborder_fix suborder_fix_max.
Proof.
rewrite /suborder_fix_max; set (A := Zo _ _).
have su: (sub (union A) E). 
  by apply: setU_s2 => y /Zo_P [q1 q2]; apply /setP_P.
have p3: (forall x, inc x A -> sub x (g (union A))). 
  move=> x /Zo_P [q1 q2];apply: (sub_trans q2); apply: gM =>//.
  by apply setU_s1;  apply: Zo_i.
have p4:  (sub (union A) (g (union A))). 
  by move=> t /setU_P [y ty yA]; move: (p3 _ yA) =>q; apply: q.
split => //; apply: extensionality => //. 
move=> t tg;move: (gS su) => p5; move: (gM  p4 p5) => p6.
by apply: (setU_i tg); apply: Zo_i => //; apply /setP_P.
Qed.


Lemma suborder_fixI: suborder_fix suborder_fix_min.
Proof.
rewrite /suborder_fix_min; set (A := Zo _ _).
have iEA: inc E A by apply: Zo_i;[ apply/setP_P | apply: gS].
have neA: nonempty A by ex_tac.
have p3 x: inc x A -> sub (g (intersection A)) x.
  move => xA; move /Zo_P: (xA)=> [/setP_P xE gg]; apply: sub_trans gg.
  by apply: (gM _ xE); apply: setI_s1.
have p4: sub (g (intersection A)) (intersection A).
  by  move => t tg; apply/(setI_P neA) => y /p3; apply.
have siE :=  (setI_s1 iEA).
have p5: inc (g (intersection A)) A. 
  by apply: Zo_i; [ apply/setP_P; apply: gS | move: (gM p4 (setI_s1 iEA))].
split => //.
apply: extensionality => // t tI; exact: (setI_hi tI p5).
Qed.


End SuborderFix.


Definition cantor_bernstein_bij_v1 X Y f g :=
   let Z:= Vfs g Y in
  let h := fun w => Vf g (Vf f w) in
  let A := Zo (\Po X) (fun x=> forall y, inc y x -> inc (h y) x)  in
  let D := intersection (Zo A (sub (X -s Z))) in
  let f4 :=  (Lf (fun y => Yo (inc y D) (h y) y) X Z) in
  inverse_fun (restriction1 g (source g)) \co f4.


Theorem CantorBernstein_v1 X Y f g :
  injection_prop f X Y -> injection_prop g Y X -> 
  bijection_prop (cantor_bernstein_bij_v1 X Y f g) X Y. 
Proof.
move=> [[ff1 if1] sf1 tf1]  [if2 sf2 tf2].
rewrite /cantor_bernstein_bij_v1.
set Z := Vfs g Y.
set f3 := inverse_fun (restriction1 g (source g)).
have f3p: bijection_prop f3 Z Y. 
  move:(restriction1_fb if2 (@sub_refl (source g))) => fb.
  apply: inverse_bij_bp; split => //; rewrite /restriction1; aw; ue.
pose h w := Vf g (Vf f w).
set (A := Zo (\Po X)(fun x=> forall y, inc y x -> inc (Vf g (Vf f y)) x)).
set D := intersection (Zo A (sub (X -s Z))).
set f4 :=  (Lf (fun y => Yo (inc y D) (h y) y) X Z).
suff f4p: (bijection_prop f4 X Z).
  exact: (compose_bp f4p f3p).
rewrite /f4; saw.
have fg := (proj1 if2).
move: (f_range_graph fg) => rg2.
move: (ImfE fg); rewrite /Imf sf2 -/Z => zv.
have FE: sub Z X by  rewrite zv -tf2; apply f_range_graph. 
have tf: (forall x, inc x X -> inc (h x) Z). 
  move=> x xs.
  apply/(Vf_image_P fg); first by rewrite - sf2;fprops.
  exists (Vf f x) => //;Wtac.
have fi:{inc X &, injective h}.
  rewrite - sf1 /g; move=> x y xs ys sg; apply: (if1 _ _ xs ys).
  apply: (proj2 if2) => //;rewrite sf2 -tf1;Wtac.
have AE:sub A (\Po X) by apply: Zo_S.
set (B:= X -s Z).
set (C:= Zo A (sub B)).
have EC: inc X C.
  apply: Zo_i; last by apply: sub_setC.
  apply: Zo_i; fprops; first by apply :setP_Ti.  
  by move => y yx; apply: FE; apply: tf.
have p1: forall x, inc x C -> sub D x.
  move=> x xC t tD; apply: (setI_hi tD xC).
have DA: inc D A.
  apply: Zop_i; first by  apply: setI_s1. 
  move=> y yD; apply: setI_i; first by ex_tac.
  move=> t tC; move: (setI_hi yD tC) => yt. 
  by move: tC => /Zo_P [] /Zo_hi tp _; apply: tp.
have DC: inc D C. 
   apply: Zo_i => //t tD; apply /setI_i ; first by ex_tac.
   by move=> y /Zo_P [_];  apply.
have BD: sub B D by move: DC => /Zo_P []. 
have cEB: (X -s B = Z) by apply: setC_K.
have Dst: (forall y, inc y D -> inc (h y) D) by move: DA => /Zo_P [].
apply: lf_bijective.
    move=> y yE /=;  Ytac yD; first by apply: tf. 
    rewrite - cEB; apply/setC_P; split => //; fprops.
  move=> u v uE vE; Ytac uD; Ytac vD => //; try (apply: fi => //).
    by move=> hi; rewrite -hi in vD; case: vD; apply: Dst.
  by move=> hi; rewrite hi in uD; case: uD; apply: Dst.
move=> y yF; move: (yF); rewrite - cEB => /setC_P [yE nyB].
case: (inc_or_not y D) => yD; last by exists y => //; Ytac0. 
have DE:sub D X by move: DA => /Zo_P [] /setP_P.
set (T:= D -s1 y). 
have BT: sub B T. 
  by move=> t tB; apply /setC1_P; split; [ apply: BD | dneg ty; rewrite -ty].
have TA: (~ (inc T A)).
  move=> TA. 
  by move: ((p1 _ (Zo_i TA BT)) _ yD) => /setC1_P [_].
have [x xT nfT]: exists2 x, inc x T & ~ (inc (h x) T).
  ex_middle bad; case: TA;apply: Zo_i => //.
    apply /setP_P; apply: sub_trans DE; apply: sub_setC.
  move=> z zT; case: (inc_or_not (h z) T) => //; move => nfzt; case:bad; ex_tac.
move: xT => /setC1_P [xD nxy].
exists x; first by apply: DE.
Ytac0;ex_middle fxy; case: nfT; apply /setC1_P; split; fprops.
Qed.

(** Alternate proof of Cantor Bernstein. 
First, any increasing function on [powerset E] has a fix-point.
Second, assume [f: E-> F] and [g: F-> E] are injections. 
There is a set [M] such that [E-M = g(F- f(M)) ]. 
The function that maps [t] to [f(t)] if [t] is not in this set, 
to the unique [y] in [F-f(M)] such that [t = g(y)] is a bijection [E-> F].
 *)

Lemma Cantor_Bernstein_aux E (g: fterm) 
  (m:= union (Zo (\Po E)(fun x=> sub x (g x)))):
  (forall x, sub x E -> sub (g x) E) ->
  (forall x y, sub x y -> sub y E -> sub (g x) (g y)) ->
  (sub m E /\ g m = m).
Proof. 
move=> p1 p2; rewrite /m; set (A := Zo _ _).
have su: (sub (union A) E). 
  by apply: setU_s2 => y /Zo_P [q1 q2]; apply /setP_P.
have p3: (forall x, inc x A -> sub x (g (union A))). 
  move=> x /Zo_P [q1 q2];apply: (sub_trans q2); apply: p2 =>//.
  by apply setU_s1;  apply: Zo_i. 
have p4:  (sub (union A) (g (union A))). 
  by move=> t /setU_P [y ty yA]; move: (p3 _ yA) =>q; apply: q.
split => //; apply: extensionality => //. 
move=> t tg;move: (p1 _ su) => p5; move: (p2 _ _ p4 p5) => p6.
by apply: (setU_i tg); apply: Zo_i => //; apply /setP_P.
Qed.


Lemma Cantor_Bernstein2_full f g
  (E:= source f) (F:= source g)
  (h:= fun x => E -s (Vfs g (F -s (Vfs f x))))
  (m:= union (Zo (\Po E) (fun x => sub x (h x))))
  (T:= Vfs g (F -s (Vfs f m))) 
  (p := fun a y => [/\ inc y F, ~ inc y (Vfs f m) & a = Vf g y])
  (f2:= Lf (fun a =>Yo (inc a T) (select (p a) F) (Vf f a)) E F):
  injection f -> injection g -> source f = target g -> source g = target f ->
  bijection_prop f2 (source f)(source g).
Proof. 
move=> [ff injf] [fg injg] sf sg.
have p1:  (forall x, sub x E -> sub (h x) E) by move=> x xE; apply: sub_setC.
have p2: (forall x y, sub x y -> sub y E -> sub (h x) (h y)). 
  move=> x y xy yE; rewrite /h => t /setC_P [tE ti]. 
  apply /setC_P;split => //; dneg aux.
  have q1: sub x (source f) by apply: sub_trans yE. 
  have pa: sub (F -s Vfs f y) (source g) by apply:sub_setC.
  have pb: sub (F -s Vfs f x) (source g) by apply:sub_setC.
  move /(Vf_image_P fg pa): aux => [u] /setC_P [uF nuy] Wu.
  apply /(Vf_image_P fg pb); exists u => //;apply /setC_P;split =>//; dneg aux2.
  move /(Vf_image_P ff q1): aux2 => [s sx ->]; apply /(Vf_image_P ff yE).
  by exists s=> //; apply: xy.
move: (Cantor_Bernstein_aux p1 p2) => [].
rewrite -/m /h -/T => mE hm.
have sc: sub (F -s (Vfs f m)) (source g) by apply: sub_setC.
set Pa := (Vf_image_P fg sc); set Pb := (Vf_image_P ff mE).
have TE: (sub T E) by move=> t /Pa [u] /setC_P [uF _] ->; rewrite /E sf; Wtac.
move: (setC_K TE); rewrite hm => cEm.
have sp: forall a, inc a T -> p a (select (p a) F).
  move => a aT; apply: (proj1 (select_pr _ _)).
    by move: aT => /Pa [u] /setC_P [uF num] Wu;ex_tac. 
  move => // x y xF [_ _ xa] yF [_ _ ya].
  by apply: injg => //; rewrite -xa -ya.
rewrite /f2/bijection_prop; saw; apply: lf_bijective.
+ move=> z zE /=;Ytac zT; [ exact (proj31 (sp _ zT)) | rewrite /F; Wtac].
+ move=> u v uE vE; rewrite /f2; Ytac uT; Ytac vT=> aux.
  - by move: (sp _ uT) (sp _ vT)=> [_ _ W1] [_ _ W2]; rewrite W1 W2 aux.
  - move: (sp _ uT) => [f1u  nf1i Wf1] ; case: nf1i; apply /Pb.
    by rewrite aux;exists v => //; rewrite -hm;apply /setC_P.
  - move: (sp _ vT) => [f1u nf1i Wf1]; case: nf1i; apply /Pb.
    by rewrite -aux;exists u => //; rewrite -hm;apply /setC_P.
  - by apply: injf.
+ move=> y yF; case: (inc_or_not y (Vfs f m)).
    move /Pb => [u um Wy]; exists u; first by apply: (mE). 
    by rewrite /f2 Y_false //;  move: um; rewrite - hm => /setC_P [].
  move=> aux; exists (Vf g y); first by rewrite /E; Wtac.  
  have wt: inc (Vf g y) T by apply /Pa; exists y => //; apply /setC_P. 
  rewrite /f2; Ytac0; move: (sp _ wt) => [q1 q2 q3].
  by symmetry; apply: injg.
Qed.

Lemma Cantor_Bernstein2 f g:
  injection f -> injection g -> source f = target g -> source g = target f ->
  equipotent (source f)(source g).
Proof. 
move => pa pb pc pd.
move:(Cantor_Bernstein2_full pa pb pc pd).
by set f0 := Lf _ _ _ => fp; exists f0.
Qed.



(* a variant of teh Cantor Bernstein theorem *)

Lemma CantorBernstein_v4 E F f g
   (gi := fun y => union (Vfi1 g y))
   (fi :=  fun y=>  union (Vfi1 f y))
   (alpha := J C0 C2) 
   (pE:= fun x => Yo (inc x (Imf g) )(J (gi x) C1) alpha)
   (pF := fun y => Yo (inc y (Imf f)) (J (fi y) C0) alpha)
   (p := fun x => Yo (Q x = C2) x (Yo (Q x = C0) (pE (P x)) (pF (P x))))
   (pn := induction_term (fun _ v => p v))
   (fv := fun x n =>
     [/\ natp n, pn x n = alpha & forall m, m <c n -> pn x m <> alpha])
   (to := fun x => exists2 n, oddp n & fv x n)
   (h1  := fun x => Yo (to x) (Vf f (P x)) (P (p x)))
   (h := fun x => h1 (J x C0)):
   injection_prop f E F -> injection_prop g F E ->
   bijection_prop (Lf h E F) E F.
Proof.
move => [[ff finj] sf tf]  [[fg ginj] sg tg].
pose E0 := indexed E C0.
pose F1 := indexed E C1.
move:C2_ne_C01 => [qa qb].
have aE0: ~inc alpha E0 by rewrite /alpha; move/setX_P => /proj33/set1_P; aw.
have aF1: ~inc alpha F1 by rewrite /alpha; move/setX_P => /proj33/set1_P; aw.
have fip x: inc x E -> fi (Vf f x) = x.
    move => xE; rewrite /fi.
    suff:  (Vfi1 f (Vf f x)) = singleton x by move ->; rewrite setU_1.
    apply: set1_pr; first by  apply:(iim_fun_set1_i ff) => //; ue.
    move => t ta; move/ (iim_fun_set1_P (Vf f x) ff): ta => [tsf eq1].
    apply: finj => //; ue.
have gip x: inc x F -> gi (Vf g x) = x.
    move => xE; rewrite /gi.
    suff:  (Vfi1 g (Vf g x)) = singleton x by move ->; rewrite setU_1.
    apply: set1_pr; first by  apply:(iim_fun_set1_i fg) => //; ue.
    move => t ta; move/ (iim_fun_set1_P (Vf g x) fg): ta => [tsf eq1].
    apply: ginj => //; ue.
have pE1 y: inc y F -> (pE (Vf g y)) = J y C1.
   rewrite /pE => yF; Ytac w; [ by rewrite gip | case:w; apply: (Imf_i fg);ue].
have pF1 x: inc x E -> (pF (Vf f x)) = J x C0.
   rewrite /pF => yF; Ytac w; [ by rewrite fip | case:w; apply: (Imf_i ff);ue].
have pE2 y: inc y F -> (p (J (Vf g y) C0)) = J y C1.
   by rewrite/p;aw; move => /pE1 ->; Ytac0; Ytac0.
have pF2 x: inc x E -> (p (J (Vf f x) C1)) = J x C0.
   by rewrite/p;aw; move => /pF1 ->; Ytac0; Ytac0.
have pa: p alpha = alpha by rewrite /p/alpha ;aw; Ytac0; Ytac0.
have pna x: pn x \0c = x by rewrite /pn induction_term0.
have pnb x n: natp n -> pn x (csucc n) = p (pn x n).
   by apply: induction_terms.
have toq x: inc x E -> (to (J x C0) <-> to (J (Vf g (Vf f x)) C0)).
   move => xE.
   have fxF: inc  (Vf f x) F by Wtac.
   have gfxE: inc (Vf g (Vf f x)) E by Wtac.
   move: (pF2 _ xE)(pE2 _ fxF);  set z := (Vf g (Vf f x)) => py pz.
   have pr: forall n, natp n ->  pn (J z C0)  (csucc (csucc n)) = pn (J x C0) n.
     apply: Nat_induction. 
       by rewrite (pnb _ _ (NS_succ NS0)) (pnb _ _ NS0) pna pna pz py.
     move => n nN hrec; rewrite (pnb _ _ nN) - hrec pnb; fprops.
   have p0: pn (J z C0) \0c <> alpha.
    by rewrite pna => /pr2_def; apply: nesym.
   have p1: pn (J z C0) \1c <> alpha.
     by rewrite - succ_zero (pnb _ _  NS0) pna pz => /pr2_def; apply: nesym.
   have qc m: natp m ->  pn (J z C0) m = alpha ->
     exists2 q, natp q & m = csucc (csucc q).            
     move => mN pp. 
     case: (equal_or_not m \0c) => m0; first by case: p0; rewrite - m0.
     move: (cpred_pr mN m0)=> [sa sb].
     case: (equal_or_not (cpred m) \0c) => m1.
       by case: p1; rewrite - pp sb m1 succ_zero.
     move: (cpred_pr sa m1) =>[sc sd]; exists (cpred (cpred m)) => //; ue.
  split; move => [n on [nN hb hc]].
    exists (csucc (csucc n)).
      by apply: succ_of_even; apply: succ_of_odd.
    split; [ fprops | by rewrite pr | move => m mls pb].
    move: (qc m (NS_lt_nat mls (NS_succ (NS_succ nN))) pb) => [q qN qv].
    move: mls; rewrite qv; move/(cltSSP (CS_succ q)(CS_succ n)).
    move/(cltSSP (CS_nat qN)(CS_nat nN)) => lqn.
    by case: (hc _ lqn);  rewrite - (pr  _ qN) - qv.
  move: (qc n nN hb) =>[q qN qv]; exists q.
     split => // eqv; case: on => _; case; rewrite qv.
     by apply: succ_of_odd; apply: succ_of_even.
  split; [ done |  by rewrite -(pr _ qN) - qv | move => m lmn].
  rewrite -(pr _ (NS_lt_nat lmn qN)).
  by apply: hc; rewrite qv; apply: cltSS ; apply: cltSS.
have hp1 x: to (J x C0) -> h x = Vf f x.
  by move => tox;rewrite /h/h1; Ytac0; aw.
have hp2 x: inc x E -> to (J x C0) -> inc (h x) F.
  move => xe tox; rewrite hp1 //;Wtac.
have hp3 x: ~ to (J x C0) -> h x = P (pE x).
  by move => rox; rewrite /h/h1/p; Ytac0; aw; Ytac0; Ytac0.
have hp7 x : inc x E -> ~ inc x (Imf g) -> to (J x C0).
  move => xE xi; exists \1c; [ by apply: odd_one | split ].
  - apply: NS1.
  - rewrite - (succ_zero) (pnb _ _ NS0) pna.
    by rewrite /p/pE; aw; Ytac0; Ytac0; Ytac0.
  - by move => m /clt1 ->; rewrite pna => /pr2_def; apply: nesym.
have hp4 x: inc x E -> ~ to (J x C0) ->
   [/\ inc x (Imf g),  h x = (gi x), inc (h x) F & Vf g (h x) = x].
  move => xE tox.
  case: (inc_or_not x (Imf g)) => xi; last by case: tox; apply: hp7.
  rewrite (hp3 _ tox).
  have-> :  P (pE x) = gi x by rewrite /pE; Ytac0; aw.
  move/(Imf_P fg):  (xi) =>[u usg uv]; rewrite sg in usg.
  by move: (gip _ usg); rewrite - uv => ->.
have hp5 x: inc x E -> inc (h x) F.
   move => xE; case: (p_or_not_p (to (J x C0))); first by apply: hp2.
   by move => tox; case: (hp4 x xE tox).
have hp6 y: inc y F -> ~ to (J (Vf g y) C0) -> y = h (Vf g y).
  move => yF hb; have xE: inc (Vf g y)  E by Wtac.
  by move: (hp4 _ xE hb) =>[hc hd he hf]; rewrite hd (gip _ yF).
have sjf y:  inc y F -> exists2 x, inc x E & y = h x.
  move => yF.
   case: (inc_or_not y (Imf f)) => yi; last first.
     set x := (Vf g y).
     have xE: inc x E by rewrite/x; Wtac.
     ex_tac.
     case: (p_or_not_p (to (J x C0))); last by move => /(hp6 y yF).
     move =>[m om [ma mb mc]].
     have eq3: p (J x C0) = J y C1 by exact: (pE2 _ yF).
     have eq4: pn (J x C0) \1c = J y C1.
       by rewrite - succ_zero (pnb _ _ NS0) pna eq3.
     have eq5: pn (J x C0) \2c = alpha.
       by rewrite - succ_one (pnb _ _ NS1) eq4 /p/pF; aw;Ytac0; Ytac0; Ytac0.
     case: (equal_or_not m \0c) => mz.
       case: om => _ []; rewrite mz; apply: even_zero.
     case: (equal_or_not m \1c) => mo.
       by move: mb; rewrite mo eq4 => /pr2_def hw; case: qb.
     move: (cge2 (CS_nat ma) mz mo); case/cle_eqVlt => mt.
       case: om => [_ []]; rewrite - mt; apply: even_two.
     by case: (mc _ mt).
   move/(Imf_P ff):  (yi) =>[x xE xv]; rewrite sf in xE.
   case: (p_or_not_p (to (J x C0))) => tox.
     by exists x => //; rewrite xv  hp1.
   set z := (Vf g y).
   have zE: inc z E by rewrite/z; Wtac.
   case: (p_or_not_p (to (J z C0))) => toz; last first.
     ex_tac; exact:(hp6 y yF toz).
   by case: tox; apply/ (toq _ xE); rewrite - xv.
saw; apply: lf_bijective => // u v uE vE sh.
case: (p_or_not_p (to (J u C0)))=> tou; case:(p_or_not_p (to (J v C0))) => tov.
- by move: sh; rewrite (hp1 _ tou) (hp1 _ tov); apply: finj; ue.
- move: sh; rewrite (hp1 _ tou) => hv.
  move: (hp4 v vE tov) =>[ra rb rc rd].
  by case: tov; rewrite - rd - hv;  apply/ (toq u uE).
- move: sh; rewrite (hp1 _ tov) => hv.
  move: (hp4 u uE tou) =>[ra rb rc rd].
  by case: tou; rewrite - rd hv;  apply/ (toq v vE).
- by rewrite -(proj44 (hp4 v vE tov)) - (proj44 (hp4 u uE tou)) sh.
Qed.  


(* variant of existence of division and substraction *)
Lemma ord_div_nonzero_b a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  a <o (b *o c)  -> b <> \0o.
Proof.
move=> oa ob oc ale bz.
by move: ale; rewrite bz oprod0l => /olt0.
Qed.


Lemma ord_div_nonzero_b_bis  a b:
  ordinalp a -> \0o <o b ->
  exists2 c, ordinalp c & a <o (b *o c).
Proof.
move=> oa bp.
move: (oprod_M1le bp (OS_succ oa)) (oltS oa);rewrite  -(osucc_pr oa) => p1 p2.
exists (a +o \1o); [ exact (proj32_1 p2) | exact (olt_leT p2 p1) ].
Qed.

Lemma odivision_exists_alt a b c:
  ordinalp a -> ordinalp b -> ordinalp c ->
  a <o (b *o c) ->
  exists q r, odiv_pr1 a b c q r.
Proof.
move=> oa ob oc [] /ordinal_le_P0; rewrite /oprod2.
set pbc:= (order_prod2 _ _) => qa qb.
move: (conj qa qb) => a_bc; clear qa qb.
have obc: worder pbc by rewrite /pbc; fprops.
move: (ordinal_lt_pr2 obc a_bc) => [f [x [xsp rgx om]]].
have orb: order (ordinal_o b) by fprops.
have orc: order (ordinal_o c) by fprops.
have ora: order (ordinal_o a) by fprops.
move: (ordinal_o_sr b) (ordinal_o_sr c) => sb sc.
move: (xsp); rewrite orprod2_sr // setX2_P.
rewrite sb sc;move=> [fgx dx xa xb].
have [w wsb wle]: exists2 w, inc w b &
  (forall t, inc t b -> gle (ordinal_o b) w t).
  have nesb: nonempty (substrate (ordinal_o b)) by rewrite sb;ex_tac.
  move:  (worder_least  (ordinal_o_wor ob) nesb)=> [w [p1 p2]]. 
  rewrite sb in p1 p2; ex_tac.  
set y := variantLc  (Vg x C0) w.
have ysp: inc y (substrate pbc).
  rewrite orprod2_sr //; apply /setX2_P; rewrite sb sc /y; aw; split;fprops.
set r := (Vg x C1) ; set q := (Vg x C0).
have lt_rb: r <o b by apply /oltP0; split => //; exact (Os_ordinal ob xb).
have lt_qc: q <o c by apply /oltP0; split => //; exact (Os_ordinal oc xa).
have oq:= proj31_1 lt_qc.
have odr:= proj31_1 lt_rb.
have worr: worder (ordinal_o r) by fprops.
have orq: order (ordinal_o q) by fprops.
have sq :=(ordinal_o_sr q).
have sqc: sub q c by move:  lt_qc => [[_ _ h] _].
have srb: sub r b  by move:  lt_rb => [[_ _ h] _].
exists q, r; split => //; split => //.
have rsub: forall r A u v, order r -> sub A (substrate r) ->
  (gle (induced_order r A) u v <-> [/\ inc u A, inc v A & gle r u v]).
  move=> r0 A0 u v or Asr; split.
    move /setI2_P => [pa] /setXp_P [ua va];split => //.
  by move=> [uA vA rr]; apply /iorder_gleP.
set A:= segment pbc y.
have iuA: A = product2 q b.
  have pa: inc C0 (doubleton C0 C1) by fprops.
  have pb: inc C1 (doubleton C0 C1) by fprops.
  set_extens u.
    move /segmentP => [] /(orprod2_gleP orb orc).
    rewrite sb sc variant_V_ca variant_V_cb.
    move=> [pc v2p h] unv.
    move: pc => /setX2_P [fgu du ua ub]; apply /setX2_P => //.
    case: h;last by move /(ordo_ltP oc ua xa).
    move=> [r1 r2]; move: (wle _ ub) => r3.
    have Wv: w =  (Vg u C1) by order_tac.
    case: unv;rewrite /y;apply: fgraph_exten => //; [fprops | by aw |].
    rewrite du; move=> x0 x0d; try_lvariant x0d; ue.
  move /setX2_P => [fgu du ua ub].
  have uc:inc (Vg u C0) c by apply: sqc.
  apply /segmentP; split; last first.
     move => uy; case: (ordinal_irreflexive oq).
     move: ua; rewrite uy /y variant_V_ca //.
  apply  /(orprod2_gleP orb orc); rewrite sb sc;split => //.
  + by apply /setX2_P. 
  + rewrite /y;apply /setX2_P;aw;split;fprops.
  + right; rewrite variant_V_ca; apply /(ordo_ltP oc uc) => //.
have ss3: substrate pbc = product2 c b by rewrite orprod2_sr // sb sc.
have ss2: sub A (substrate pbc) by apply: sub_segment.
have sA: sub A (product2 c b) by ue.
have wo2: worder (induced_order pbc A) by apply: induced_wor.
have obq: ordinalp (b *o q) by fprops.
have ->:b *o q = ordinal (induced_order pbc A).
  symmetry; apply: ordinal_o_isu2 => //. 
  set r1 :=  (order_prod2 (ordinal_o b) (ordinal_o q)).
  have wo1: worder r1 by rewrite /r1; fprops.
  apply: orderIT (ordinal_o_is wo1).
  have or2:order (induced_order pbc A) by fprops.
  have or1:order r1 by fprops.
  suff: r1 = (induced_order pbc A) by move=> ->; apply: orderIR.
  apply: order_exten => // u v; split.
    move /(orprod2_gleP orb orq);rewrite sb sq; move => [pa pb pc].
    apply /iorder_gle0P; try ue; apply /(orprod2_gleP orb orc).
    rewrite sb sc; split => //; try( apply :sA ; ue).
    case: pc; [ by left | move => [ /ordo_leP [sa ssb ssc] sd] ; right ].
    split => //;apply /ordo_leP;split;fprops.
  move => /iorder_gleP [uA vA] /(orprod2_gleP orb orc) [_ _ h].
  apply /(orprod2_gleP orb orq); rewrite sb sq;split => //; try ue.
  case: h; [by left | move=> [/ordo_leP [sa ssb ssc] sd]; right].
  move: uA vA;rewrite iuA;move /setX2_P => [_ _ uq _] /setX2_P [_ _  vq _].
  split => //;apply /ordo_leP;split;fprops.
set C := induced_order pbc (segment pbc x).
have oraC: C \Is (ordinal_o a).
  have injf:= (order_morphism_fi om).
  move: om=> [o1 o2 [ff sf tf] mof].
    apply: orderIS; rewrite /C -rgx.  
  have sr: sub (Imf f) (substrate pbc).
     rewrite - tf; fprops; apply: Imf_Starget =>//.  
  have o3:= (proj1(iorder_osr o2 sr)).
  have aux: (source (restriction1 f (source f))) = source f.
     by rewrite  /restriction1; aw.
  exists (restriction1 f (source f)); split => //.
   hnf; rewrite{2 3}/restriction1 iorder_sr //; saw.
   by apply:(restriction1_fb injf).
  red; rewrite aux => u v usf vsf;rewrite restriction1_V // restriction1_V //.
  rewrite /pbc mof // rsub //; split; last by move => [_ _].
  move=> Wuv; split => //; Wtac. 
rewrite - (ordinal_o_o oa) -(ordinal_o_o odr).
have opbc: order pbc by fprops.
symmetry;apply: orsum_invariant5 => //. 
apply: orderIT oraC.
set fo:= order_sum2 _ _.
have sfo: substrate fo = canonical_du2 A r.
  by  rewrite /fo orsum2_sr//? iorder_sr //; fprops; rewrite ordinal_o_sr.
have ysp': inc y (product2 c b) by ue.
have xsp': inc x (product2 c b) by ue.
have lexy: gle pbc y x.
  apply /(orprod2_gleP orb orc); rewrite sb sc /y;aw; split => //; left. 
  by split => //;apply: wle.
have ltAx: forall t, inc t A -> glt pbc t x.
   move =>t /segmentP lttxy; order_tac.
have rprop: forall z, inc z r -> inc (variantLc (Vg x C0) z) (product2 c b).
  move=> z zB; apply /setX2_P; aw; split;fprops.
have p1: forall z, inc z r -> gle pbc  y (variantLc (Vg x C0) z).
  move=> z zB; apply /(orprod2_gleP orb orc); rewrite sb sc; split;fprops.
  by rewrite /y;aw;left; split => //; apply: wle; apply: srb.
set g := fun z => Yo (Q z = C0) (P z) (variantLc (Vg x C0) (P z)).
have ssx: sub (segment pbc x) (substrate pbc) by apply: sub_segment.
have srC: substrate C = (segment pbc x) by rewrite /C iorder_sr.
have ta: forall z, inc z (substrate fo) -> inc (g z) (substrate C).
  move=> z; rewrite sfo; move /candu2P=> [pz xx].
  rewrite srC; apply /segmentP;case :xx.
    by move => [Pz Qz]; rewrite /g; Ytac0;apply: ltAx => //.
  move => [Pz Qz]; rewrite /g Qz; Ytac0; split; last first.
    by move => bad; case: (ordinal_irreflexive odr); rewrite {1} /r -bad; aw.
  apply /(orprod2_gleP orb orc); rewrite sb sc.
  move /(ordo_ltP ob (srb _ Pz) xb): (Pz) => [pa pb].
  split; [ by apply: rprop | exact | left].
  by rewrite variant_V_ca variant_V_cb.
have bg: bijection (Lf g (substrate fo) (substrate C)).
  apply: lf_bijective => //.
    move=> u v; rewrite sfo /g; move /candu2P => [pu p3]  /candu2P [pv p4].
    case: p3; case: p4; move=> [p5 p6][p7 p8];rewrite p6 p8; Ytac0; Ytac0=> aux.
    + by apply: pair_exten =>//;  ue.
    + move/segmentP: p7 => lt1;move:(p1 _ p5);rewrite -aux => lt2; order_tac.
    + move/segmentP:p5 => lt1; move:(p1 _ p7); rewrite aux => lt2; order_tac.
    + by apply: pair_exten => //; [ move: (f_equal (Vg ^~ C1) aux); aw | ue ].
  move=> v; rewrite srC => /segmentP hyp.
  case: (p_or_not_p (glt pbc v y)) => aux.
    exists (J v C0); last by rewrite /g; aw; Ytac0.
    rewrite sfo; apply /candu2P; split;fprops;left. 
    by saw; apply /segmentP.
  move: hyp aux => [] /(orprod2_gleP orb orc); rewrite sb sc.
  move => [vp xp aux] nvx cvy.
  case: aux; last first.
    move=> aux2; case: cvy.
    split; last by rewrite /y;move: aux2 =>[_ vx]; dneg ww; rewrite ww; aw.
    apply /(orprod2_gleP orb orc);  rewrite sb sc.
    by split => //;rewrite /y; aw; right.
  move=> [sva leva].
  have vpr: v = variantLc (Vg x C0) (Vg v C1).
    move: vp => /setX2_P [a1 a2 a3 a4].
    apply: fgraph_exten => //;[ fprops | by aw |]. 
    by rewrite a2;  move => z zd; try_lvariant zd.
  have ltva:glt (ordinal_o b) (Vg v C1) (Vg x C1).
    split => //; clear cvy; dneg ww; rewrite vpr ww.
    symmetry; move:xp => /setX2_P [a1 a2 _ _].
    apply: fgraph_exten => //;[ fprops | by aw |]. 
    by rewrite a2;  move => z zd; try_lvariant zd.
  exists (J  (Vg v C1) C1); last by rewrite /g; aw; rewrite -vpr; Ytac0.  
  rewrite sfo;apply: candu2_prb => //.
  move /ordo_leP: leva => [pa pb pc].
  by apply /(ordo_ltP ob pa pb).
exists (Lf g (substrate fo) (substrate C)).
  apply: total_order_isomorphism; rewrite ? lf_source ? lf_target //.
    rewrite /fo;apply: orsum2_totalorder => //.
      apply: total_order_sub => //;apply: worder_total => //.
      apply: worder_total => //.
  apply: (proj1 (iorder_osr opbc ssx)).
rewrite sfo; rewrite sfo in ta.
have oiA: order (induced_order pbc A) by fprops.
have oor:  order (ordinal_o r) by fprops.
move=> u v uc vc /=; rewrite LfV // LfV // /fo /C rsub //.  
move /orsum2_gleP => [_ _ h]; rewrite - srC;split => //; try (apply: ta => //).
rewrite /g; case: h. 
    move=> [h1 h2 h3]; Ytac0; Ytac0; apply: (iorder_gle1 h3).
  move=> [h1 h2 h3];  Ytac0; Ytac0.
  apply /(orprod2_gleP orb orc); rewrite sb sc; aw.
  move /ordo_leP: h3 => [h3 h4 h5].
  split; [by apply: rprop | by apply: rprop | left; split => //].
  by apply /ordo_leP; split => //;  apply: srb.
move => [h1 h2]; Ytac0; Ytac0.
move/candu2P: uc => [_]; case; last by move => [_ bad]; case: C1_ne_C0; ue.
move => [/segmentP [pa _] _].
move/candu2P: vc => [_];case; [ by move=> [_] | move=> [/p1 h0 _]; order_tac].
Qed. 


Lemma order_diff_p1 A r 
  (r1 := induced_order r A)
  (r2 := induced_order r ((substrate r) -s A)):
  total_order r -> segmentp r A ->
  r \Is order_sum2 r1 r2.
Proof.
move => [or tor] segf.
set B := substrate r -s A.
have sbF:sub B (substrate r) by move => t /setC_P [].
have saF:sub A (substrate r) by exact: (proj1 segf).
move: (iorder_osr or saF) => [orA srA].
move: (iorder_osr or sbF) => [orB srB].
apply:orderIS.
case:(orsum2_osr orA orB).
set r5 := order_sum2 _ _ => or5 sr5'.
move:(sr5'); rewrite ! iorder_sr //; move => sr5.
have ax: forall x, inc x (substrate r5) -> inc (P x) (substrate r).
   rewrite sr5 => x /candu2P [_]; case => [] [pp _]; fprops.
exists (Lf P (substrate r5) (substrate r)); split => //.
  saw; apply: lf_bijective.
   - exact.
   - rewrite sr5;move => x  y /candu2P [px pxx] /candu2P [py pyy] sp.
     apply: (pair_exten px py sp).
     case: pxx => [][qa ->]; case: pyy => [][qb ->] //.
       by case/setC_P: qb => _; rewrite - sp.
     by case/setC_P: qa => _; rewrite  sp.
   - rewrite sr5;move => y ysr2; case: (inc_or_not y A) => yA.
       by exists (J y C0); aw;trivial; apply: candu2_pra.
      by exists (J y C1); aw; trivial;apply: candu2_prb; apply:setC_i.
hnf; aw;  move => x y xs ys; rewrite !LfV//.
move:(xs); rewrite sr5 => /candu2P [xa xb].
move:(ys); rewrite sr5 => /candu2P [ya yb].
move:(orsum2_gleP (induced_order r A) (induced_order r B) x y).
rewrite - sr5' -/r5 => H; split.
   move: C1_ne_C0 => ba; move:(nesym ba) => bb.
   move/H => [_ _]; case.
   + by move => [_ _]; case/iorder_gleP.
   + by move => [_ _]; case/iorder_gleP.
   + move => [qx qy]; case: xb; last by rewrite qx;move => [_] //.
     case: yb => [] [pyb] // _ [pxa _].
     have pxr: inc (P x) (substrate r) by apply: saF.
     have pyr: inc (P y) (substrate r) by apply: sbF.
     case: (tor (P x) (P y) pxr pyr) => // lpp.
     case/setC_P: pyb =>_ []; exact:(proj2 segf (P x) (P y) pxa lpp).
move => lexy; apply/H; split => //.
case: yb => [] [yA ->].
  move: (proj2 segf (P y) (P x) yA lexy) => xA.
  constructor 1; split.
   + by case: xb => [][] //;case/setC_P.
   + done.
   + by apply/iorder_gleP.
case: xb => [] [xA ->]; first by constructor 3; split => //; fprops.
by constructor 2; split => //; fprops;apply/iorder_gleP.
Qed.

Lemma order_diff_p2 r1 r2 f
      (r3 := induced_order r2 ((substrate r2) -s (Imf f))):
  worder r1 -> worder r2 ->
  order_morphism f r1 r2 -> segmentp r2 (Imf f) ->
  worder r3 /\  r2 \Is order_sum2 r1 r3.
Proof.
move => ow1 ow2 omf.
have ijf:=(order_morphism_fi omf).
move:omf => [or1 or2 [ff sf tf] sif segf].
rewrite/r3; set A := (Imf f); set B := substrate r2 -s A.
have sbF:sub B (substrate r2) by move => t /setC_P [].
have saF:sub A (substrate r2) by exact: (proj1 segf).
have ha:=  (induced_wor ow2 sbF).
split => //.
have hb:= (induced_wor ow2 saF).
have hbb:= proj1 hb.
have haa:= proj1 ha.
have res1: r1 \Is (induced_order r2 A).
  have lax: lf_axiom (Vf f) (source f) A.
    by move => t ts; apply/(Imf_P ff); ex_tac.
  exists(Lf (Vf f) (substrate r1) A).
  split => //.
    rewrite iorder_sr//;  saw; rewrite - sf;apply:lf_bijective.
    - done.
    - move => u  v usf vsf sv; exact: (proj2 ijf _ _ usf vsf sv).
    - by move => y /(Imf_P ff).
  hnf; aw;rewrite - sf;move => x y xE yE; rewrite !LfV//.
  apply:(iff_trans (sif x y xE yE)) .
  apply:iff_sym; exact:(iorder_gle0P r2 (lax _ xE) (lax _ yE)).
apply:(orderIT (order_diff_p1 (worder_total ow2) segf)).
apply (orsum_invariant4 (orderIS res1) (orderIR haa)).
Qed.


Lemma odiff_pr_alt a b 
  (c := ordinal (induced_order (ordinal_o b) (b -s a))):
  a <=o b -> (ordinalp c /\ b = a +o c).
Proof.
move => [oa ob ab].
set F:= b -s a.
set B := ordinal_o b.
have wB: worder B by rewrite /B;fprops.
move: (ordinal_o_sr b); rewrite -/B => sB.
have Es: sub a (substrate B) by ue.
have Fs: sub F (substrate B) by rewrite sB; apply: sub_setC.
set r := induced_order B a.
set r' := induced_order B F.
have wor: worder r by apply: induced_wor.
have wor': worder r' by apply: induced_wor.
have -> : c = ordinal r'  by done.
set A:= ordinal r; set C := ordinal r'.
have oA: ordinalp A by apply: OS_ordinal.
have oC: ordinalp C by apply: OS_ordinal.
split; first by exact.
have ra : r = ordinal_o a.
  apply: order_exten; fprops.
  move => x y; split => le1.
    move: (iorder_gle3 le1) => [p1 p2].
    move: (iorder_gle1 le1) => /ordo_leP [_ _ h]; apply /ordo_leP;split => //.
  move /ordo_leP: le1 => [pa pb pc]; apply /iorder_gle0P => //.
  apply /ordo_leP;split;fprops.
have <-: A = a by rewrite /A ra; apply: ordinal_o_o.
rewrite /A/C - (ordinal_o_o ob).
symmetry; apply: orsum_invariant5 => //.
have orb: order B by fprops.
have or: order r by fprops.
have or': order r' by fprops.
have sr: substrate r = a by rewrite /r iorder_sr.
have sr': substrate r' = F by rewrite /r' iorder_sr.
have ta: forall x, inc x (substrate (order_sum2 r r')) 
   -> inc (P x) (substrate B).
  move=> x; rewrite orsum2_sr // => /candu2P; rewrite sr sr'.
  by move=> [_ ]; case; move=> [pqx _]; [apply: Es |apply: Fs].
exists (Lf P  (substrate (order_sum2 r r')) (substrate B)).
have xxa: total_order (order_sum2 r r').
  by apply: orsum2_totalorder; apply: worder_total.
have xxb:bijection (Lf P (substrate (order_sum2 r r')) (substrate B)).
  apply: lf_bijective => //.
    move=> x y;rewrite orsum2_sr //;move /candu2P=> [px h1] /candu2P [py h2] sp.
    apply: pair_exten =>//.
    case: h1; case: h2; move=> [Px Qx][Py Qy];rewrite Qx Qy //.
      by move: Px Py; rewrite sr sr' /F - sp;  move /setC_P => [].
      by move: Px Py; rewrite sr sr' /F - sp => aux; move /setC_P => [].
  move=> y ysb; case: (inc_or_not y a) => yE.
    exists (J y C0); last by aw. 
    by rewrite orsum2_sr //; apply candu2_pra; rewrite sr.
  have yF: inc y F by rewrite /F - sB; apply /setC_P; split.
  exists (J y C1); last by aw. 
  by rewrite orsum2_sr //; apply :candu2_prb; rewrite sr'.
apply: total_order_isomorphism => //; aw; trivial.
move=> x y xsr ysr /=; rewrite LfV //  LfV //.
move: xsr ysr;  rewrite orsum2_sr //; move=> xsr ysr => ha.
move /orsum2_gleP:ha => [_ _ ]; case.
    by move=> [_ _ h1]; move: (iorder_gle1 h1).
  by move=> [_ _ h1]; move: (iorder_gle1 h1).
move => [qxa qyb].
move: xsr ysr => /candu2P [px h1] /candu2P [py h2].
case: h1; last by move=> [_];  rewrite qxa => aux; case: C0_ne_C1.
case: h2; first by move=> [_ xx]; rewrite xx in qyb; case: qyb. 
rewrite sr sr'; move=> [Py _] [Px _ ].
move: (worder_total wB)=> [_ tob].
have xb: inc (P x) (substrate B) by apply:  Es.
have yb: inc (P y) (substrate B) by apply:  Fs.
case: (tob _ _ xb yb) => //.
move: Py => /setC_P [_ nya] /ordo_leP [iyb ixb xy]; case: nya.
case:  (ordinal_sub (Os_ordinal ob iyb)  (Os_ordinal ob ixb) xy).
  by move=> ->.
apply: (ordinal_transitive oa Px).
Qed.

Lemma odiff_wrong_alt a b
  (c := ordinal (induced_order (ordinal_o b) (b -s a))):
  b <=o a -> c = \0c.
Proof.
rewrite /c; move=> [oa ob ab];rewrite (setC_T ab).
have oon: order (ordinal_o b) by apply: ordinal_o_or.
apply: ordinal0_pr1; rewrite iorder_sr; fprops.
Qed.

Lemma osum_limit_alt x y: ordinalp x -> limit_ordinal y -> 
  limit_ordinal (x +o y).
Proof.
move=> ox ly.
move:(proj31 ly) => oy.
case: (ozero_dichot ox) => xz; first by rewrite xz osum0l //. 
move /limit_ordinal_P:ly => [ ynz yl]. 
move: (@osum_Meqlt \0o y x ynz ox); rewrite (osum0r ox) => lt0.
apply /limit_ordinal_P; split; first exact: (olt_ltT xz lt0).
move => z lt1.
have y1: \1o <o y by rewrite - osucc_zero; apply: yl. 
have oz:= proj31_1 lt1.
rewrite - (osucc_pr oz).
case: (oleT_ee oz ox) => zx.
  exact (ole_ltT (osum_Mleeq zx OS1) (osum_Meqlt y1 ox)).
move: (odiff_pr zx) => [pd pe].
rewrite pe in lt1.
move: (yl _ (osum_Meqltr pd oy ox lt1)). 
rewrite - (osucc_pr pd) => pg.
by move: (osum_Meqlt pg ox);  rewrite (osumA ox pd OS1) -pe.
Qed.


(** Injectivity of cardinal successor, according to Bourbaki *)

Lemma succ_injective2 a b: cardinalp a ->  cardinalp b -> 
  a +c \1c = b +c \1c -> a = b.
Proof. 
move=> ca cb hyp.
suff: equipotent a b.
  by move/card_eqP; rewrite (card_card ca) (card_card cb).
move: (disjointU2_pr3 a card_one C1_ne_C0) => eq1. 
move: (disjointU2_pr3 b card_one C1_ne_C0) => eq2.
rewrite -hyp in eq2; clear hyp.
move: (esym eq1) => /card_eqP [f [bf sf tf]] {eq1}.
move: (esym eq2)=> /card_eqP[g [bg sg tg]] {eq2}.
set (A0:= Vfs f (a *s1 C0)).
set (B0:= Vfs g (b *s1 C0)).
rewrite /card_one in sf sg.
set xA:= J emptyset C0; set xB:=  J emptyset C1.
have main: (forall c h, bijection h -> source h =
    (c *s1 C0) \cup  ((singleton emptyset) *s1 C1) ->
    let w:= Vfs h (c *s1 C0) in
      let v:= Vf h xB in
       [/\  ~(inc v w),  target h = w \cup (singleton v) & c \Eq w]).
  move=> c h bh sh w v.
  move: (bij_function bh)=> fh. 
  have  sh1:sub (c *s1 C0) (source h) by rewrite sh; apply: subsetU2l.
  have sh2: inc xB (source h).
    rewrite sh; apply: subsetU2r; rewrite /xB;apply /indexed_P;aw;split;fprops.
  split. 
    move /(Vf_image_P fh sh1) => [u vs vw]. 
    have uW: (u = xB).
      by move: bh=> [[ _ ih] _]; apply: ih=>//; apply: sh1.
   move: vs; rewrite uW; move /indexed_P=> [_ _]; rewrite /xB; aww.
    set_extens t. 
      move:bh => [_ sjh] tt; move:((proj2 sjh) _ tt)=> [y ys hy].
      rewrite sh in ys; case /setU2_P: ys => p.
        apply /setU2_P; left; rewrite hy; apply  /(Vf_image_P fh sh1); ex_tac.
      have yp: y = xB.
        move:p => /indexed_P; aw; move => [py Py Qy]. 
        by apply: pair_exten; rewrite /xB; aww; move /set1_P: Py.
      rewrite hy yp -/v; apply /setU2_P; right; fprops.
    case /setU2_P.
      move /(Vf_image_P fh sh1)=> [u us ->]; Wtac.
    move /set1_P=> ->; rewrite /v; Wtac.
  apply: (EqT (Eq_indexed c C0)).
  exists (restriction1 h (c *s1 C0));split. 
    by apply: restriction1_fb; move: bh => [ih _].
    by rewrite /restriction1; aw. 
    by rewrite /restriction1; aw. 
apply/card_eqP.
move: (main _ _ bf sf) (main _ _ bg sg); clear main.
simpl; fold A0 B0.
move=> [nWxfA0 tfA /card_eqP ->][nWxfB0 tgB /card_eqP ->].
have tfg: target f = target g by ue.
case: (equal_or_not (Vf f xB) (Vf g xB))=> efg.
  suff: (A0 = B0) by move=> ->.
  set_extens t => ts.  
    have : (inc t (target f)) by rewrite tfA;  apply: subsetU2l.
    rewrite tfg tgB;case /setU2_P =>//. 
    move /set1_P;rewrite -efg =>tv; case: nWxfA0; ue.
  have : (inc t (target f)) by rewrite tfg tgB; apply: subsetU2l.
  rewrite tfA; case /setU2_P =>//. 
  move /set1_P; rewrite efg =>tv; case: nWxfB0; ue.
set (C0:= A0 \cap B0). 
have ->: (A0 = C0 \cup (singleton (Vf g xB))). 
  set_extens t => ts. 
     have : (inc t (target f)) by rewrite tfA;apply: subsetU2l.
     rewrite tfg tgB; case /setU2_P.
     by move=> tB; apply :setU2_1; apply: setI2_i.
     move /set1_P => ->; apply /setU2_P; right; fprops.
  case /setU2_P: ts; first by move/ setI2_P => [].
  move /set1_P => tu.
  have: (inc t (target f)). rewrite tfg  tgB tu; fprops.
  by rewrite tfA; case/setU2_P =>// /set1_P tw; case: efg; rewrite -tu -tw.
have ->: (B0 = C0 \cup (singleton (Vf f xB))).
  set_extens t => ts. 
     have : (inc t (target g)) by rewrite tgB;apply: setU2_1.
     rewrite -tfg tfA; case /setU2_P.
       by move=> tB; apply: setU2_1; apply: setI2_i.
     move /set1_P => ->; apply /setU2_2; fprops.
  case /setU2_P: ts; first by move /setI2_P => [].
  move /set1_P =>  tu.
  have: (inc t (target f)).
       rewrite tfA; apply: setU2_2; aw; ue. 
  rewrite tfg tgB; case /setU2_P =>// /set1_P tw.
  by case: efg; rewrite -tu -tw.
rewrite !csucc_pr //;move /setI2_P => [] //.
Qed.


End Misc2.



Module CantorCompare.

(** Let [E] be an ordered set and [ssub F] the set of strict upper bounds of [F].

Cantor says that [E] is well-ordered if [E] has a least element and, for any 
non-empty subset [F], if [ssub F] is not empty, it has a least element. 
This agrees with the standard definition *)

Lemma cantor_worder r 
   (ssub := fun E => Zo (substrate r)(fun z => forall x, inc x E -> glt r x z)):
   order r -> nonempty (substrate r) -> 
   ( worder r <->
    ( (has_least r)
     /\ (forall F, sub F (substrate r) -> nonempty F -> nonempty (ssub F) ->
       (has_least (induced_order r (ssub F)))))).
Proof.
move => or nesr; split.
  move => [_ wor ]; split;first by apply: worder_least.
  move => F sfr nef nef1; apply: wor => //; apply: Zo_S.
move => [[y [ysr ly]] pb]; split => //.
move => x xsr [x0 x0x].
case: (inc_or_not y x).
  move => yx; exists y; red; rewrite (iorder_sr or xsr); split => //.
  by move => t tx; apply /iorder_gle0P => //; apply: ly; apply: xsr.
move => nyx.
set F:= Zo (substrate r)  (fun z => forall t, inc t x -> glt r z t).
have sf1: sub F (substrate r) by apply: Zo_S.
have yf1: inc y F.
  apply: Zo_i => // t tx; split; [ apply: (ly _ (xsr _ tx)) | dneg yt; ue].
set G := ssub F.
have pa : sub x G.
  move => t tx; apply: Zo_i; first by apply: xsr.
  by move => tv /Zo_P [_ aux]; apply: aux.
have neG: nonempty G by exists x0; apply: pa.
have neF: nonempty F by exists y.
have sg: sub (ssub F) (substrate r) by apply: Zo_S.
move: (pb _ sf1 neF neG) => [a []]; rewrite (iorder_sr or sg) => aG h.
exists a; hnf; rewrite (iorder_sr or xsr).
have qa: forall t, inc t x -> gle r a t.
  move => t tx.
  move: (h _ (pa _ tx)) => cp1; exact (iorder_gle1 cp1).
case: (inc_or_not a x) => iax.
  by split => // t tx; apply /iorder_gle0P => //; apply: qa.
have aF: inc a F.
  apply: Zo_i; [by apply: sg | move => t tx; split;[ by apply: qa| dneg ta;ue]].
by move: aG => /Zo_P [_ p]; move: (p _ aF) => [_].
Qed.

Lemma Cantor_aux r X f x: worder r -> fsiso_prop f r (induced_order r X)  ->
  source f = substrate r ->  glt r (Vf f x) x -> False.
Proof.
move => wor fsi sf lt1.
have xsr := (arg2_sr (proj1 lt1)). 
set E := Zo (substrate r) (fun z => glt r (Vf f z) z).
have ses: sub E (substrate r) by apply: Zo_S.
have ne: nonempty E by exists x; apply: (Zo_i xsr). 
move: (worder_prop wor ses ne) =>[a /Zo_P [asr av] al].
move: asr (arg1_sr (proj1 av)); rewrite - sf => asf bsf.
have bE: inc (Vf f a) E.
  apply: Zo_i; first by ue.
  by move /(fsi (Vf f a) a bsf asf): av => /iorder_gltP [].
exact: (not_le_gt (proj1 wor) (al _ bE) av).
Qed.

Lemma CantorA r r' f x (y := Vf f x):
  order_isomorphism f r r' ->
  inc x (substrate r) -> 
  (seg_order r x) \Is (seg_order r' y).
Proof.
move => h xsr.
move: (order_isomorphism_siso h) => fsi.
move: h => [or1 or2 [bf sf tf] fi].
have ff := proj1 (proj1 bf).
move: (seg_order_osr x or1) =>[ra rb].
move: (seg_order_osr y or2) =>[rc rd].
have sSx: sub (segment r x) (source f) by rewrite sf; apply: sub_segment.
have sSy: sub (segment r' y) (target f) by rewrite tf; apply: sub_segment.
have xsf: inc x (source f) by ue.
have ax0 u: inc u (segment r x) -> inc (Vf f u) (segment r' y).
  move=> ux;by apply/segmentP; apply/(fsi _ _ (sSx _ ux) xsf); apply/segmentP.
have ax: restriction2_axioms f (segment r x) (segment r' y).
  by split => // t; move /(Vf_image_P ff sSx) => [u ux ->]; apply: ax0.
case: (restriction2_prop ax). set g := restriction2 _ _ _ => fg sg tg.
have bg: bijection g.
  split; first exact: (restriction2_fi (proj1 bf) ax).
  split => //; rewrite tg sg => u ust.
  move: (proj2 (proj2 bf) u (sSy _ ust))=>[v vsf eq1].
  have vSx: inc v (segment r x).
    by apply/segmentP; apply/(fsi _ _ vsf xsf); rewrite - eq1; apply/segmentP.
  by ex_tac; rewrite (restriction2_V ax vSx).
exists g; split => //; first by hnf; rewrite rb rd.
move => u v; rewrite sg => usx vsx; move: (ax0 _ usx)(ax0 _ vsx) => usy vst.
rewrite (restriction2_V ax usx)(restriction2_V ax vsx).
apply: (iff_trans (iorder_gle0P r usx vsx)).
apply: (iff_trans (fi u v (sSx _ usx)  (sSx _ vsx))).
by apply: iff_sym; apply: iorder_gle0P.
Qed.


Lemma CantorB_1 r x: worder r -> inc x (substrate r) -> 
  r \Is (seg_order r x) -> False.
Proof.
move => wor xsr [f h].
move: (h) =>  [or or1 [[[ff _] _]  sf tf] fi].
have xs: glt r (Vf f x) x.
  apply/segmentP;rewrite - (proj2(seg_order_osr x or)) - tf; Wtac.
exact: (Cantor_aux wor (order_isomorphism_siso h) sf xs).
Qed.
  
Lemma CantorB r x: worder r -> inc x (substrate r) -> 
  r \Is (seg_order r x) -> False.
Proof.
move => wor xsr fiso.
have or := proj1 wor.
set E := Zo (substrate r) (fun z => r \Is (seg_order r z)).
have ses: sub E (substrate r) by apply: Zo_S.
have ne: nonempty E by exists x; apply: Zo_i.
move: (worder_prop wor ses ne) =>[a /Zo_P [asr isa] al]  {fiso xsr}.
move: (seg_order_osr a or) => [oo eq1].
move: (isa) => [f ff]; move:(ff) => [_ _ [bf sf tf] _].
have asf: inc a (source f) by ue.
move: (Vf_target (proj1 (proj1 bf)) asf); rewrite tf eq1 => /segmentP lt1.
move: (CantorA ff asr); rewrite (seg_order_trans or lt1)  => gp.
move:(orderIT isa gp) => ci.
have:inc (Vf f a) E by apply: (Zo_i (arg1_sr (proj1 lt1))).
move/al => be;exact: (not_le_gt or be lt1).
Qed.
 

Lemma CantorC_1 r x X: worder r -> inc x (substrate r) -> sub X (segment r x) ->
  r \Is (induced_order r X) -> False.
Proof.
move => wor xsr Xsk [f h].
move: (h) =>  [or or1 [[[ff _] _] sf tf] fi].
have xs: glt r (Vf f x) x.
  apply/segmentP; apply: (Xsk).
  rewrite - (iorder_sr or (sub_trans Xsk (@sub_segment r x))) - tf; Wtac.
exact: (Cantor_aux wor (order_isomorphism_siso h) sf xs).
Qed.


Lemma CantorC r x X: worder r -> inc x (substrate r) -> sub X (segment r x) ->
  r \Is (induced_order r X) -> False.
Proof.
move => wor xsr Xsr iso.
set E := Zo (substrate r)
   (fun z => exists2 X, sub X (segment r z) & r \Is (induced_order r X)).
have ses: sub E (substrate r) by apply: Zo_S.
have ne: nonempty E.
  by exists x; apply: (Zo_i xsr); exists X.
clear x X xsr Xsr iso.
move: (worder_prop wor ses ne) =>[x /Zo_P [xsr [X Xsr [f fiso]]] xl].
move:(fiso) => [or _ [bf sf tf] _].
have asf: inc x (source f) by ue.
move: (sub_trans Xsr (@sub_segment r x)) => Xs.
move: (proj2(seg_order_osr x or)) => eq1.
move: (iorder_sr or Xs) => eq2.
move: (Vf_target (proj1 (proj1 bf)) asf); rewrite tf eq2 => inc1.
move /segmentP: (Xsr _ inc1) => lt1.
move: (arg1_sr (proj1 lt1)) => fxsr.
suff: inc (Vf f x) E by move/ xl => le1;exact: (not_le_gt or le1 lt1).
move: (CantorA fiso xsr) =>[g].
set A := (segment (induced_order r X) (Vf f x)).
set B := (segment r (Vf f x)).
have sAB: sub A B.
  by move=> t/segmentP/iorder_gltP [ _ _/segmentP].
have sAX: sub A X by move => t/segmentP /iorder_gltP [].
have sr1: sub (segment r x) (substrate r) by apply: sub_segment.
have sr2:= sub_trans sAX Xs.
rewrite /seg_order (iorder_trans _ sAX).
move =>[or1 or2]; rewrite iorder_sr // iorder_sr //; move => [bg sg tg] pb.
have fg: function g by fct_tac.
have Xsg: sub X (source g) by rewrite sg.
move: (restriction1_fb (proj1 bg) Xsg) => bh.
move:(restriction1_prop fg Xsg) =>[fh sh th].
have ss: sub  (Vfs g X) A by rewrite - tg; apply: fun_image_Starget1.
have hiso: order_isomorphism  (restriction1 g X) 
  (induced_order r X)(induced_order r (Vfs g X)).
  move:(iorder_osr or Xs) =>[sa sb].
  move:(iorder_osr or (sub_trans ss sr2)) =>[sc sd].
  split => //; first by rewrite sb sd.
  move => u v; rewrite sh => ux vx.
  rewrite (restriction1_V fg Xsg ux) (restriction1_V fg Xsg vx).
  apply: (iff_trans (iorder_gle0P r ux vx)).
  move: (pb u v (Xsg _ ux) (Xsg _ vx)) => aux.
  move:(iff_trans (iff_sym (iorder_gle0P r (Xsr _ ux) (Xsr _ vx))) aux) => h.
  have se: inc (Vf g u) (Vfs g X) by apply/(Vf_image_P fg Xsg); exists u.
  have si: inc (Vf g v) (Vfs g X) by apply/(Vf_image_P fg Xsg); exists v.
  have sj: inc (Vf g u) A by Wtac.
  have sk: inc (Vf g v) A by Wtac.
  split.
    by move/h => /iorder_gleP [qa qb qc]; apply/iorder_gleP.
  by move/iorder_gleP =>[_ _ lr4]; apply /h; apply/iorder_gleP.
apply: (Zo_i fxsr); exists (Vfs g X). 
  exact: (sub_trans ss sAB).
exists  (restriction1 g X \co f).
exact:(compose_order_is fiso hiso).
Qed.


Lemma CantorD r x y: worder r -> inc x (substrate r) -> inc y (substrate r) ->
   (seg_order r x) \Is  (seg_order r y) ->  x = y.
Proof.
move => wor xsr ysr.
suff H: forall a b,   glt r a b ->
   (seg_order r a) \Is (seg_order r b) -> False.
  move =>h; ex_middle bad.
  case:(proj2(worder_total wor) x y xsr ysr) => le.
    case:(H _ _  (conj le bad) h). 
    case:(H _ _  (conj le (nesym bad)) (orderIS h)).
move => a b ltab {xsr ysr} ois.
have or := proj1 wor.
have asb: inc a (segment r b) by apply/segmentP.
move: (seg_order_wor b wor)(seg_order_osr b or) => wor' [or' sr'].
have asr': inc a (substrate (seg_order r b)) by ue.
apply: (CantorB  wor' asr'); apply: orderIS.
by rewrite seg_order_trans.
Qed.

  
Lemma CantorE r r' f f': worder r -> worder r' ->
  order_isomorphism f r r' ->  order_isomorphism f' r r' -> f = f'.
Proof.
move => wor1 wor2 is1 is2.
move: (is1) (is2) =>[_ _ [[[ff _] _]sf tf] _ ] [_ _ [[[ff' _] _] sf' tf'] _ ].
apply: function_exten=> //; (try ue); rewrite sf => x xsr.
have fxr: inc (Vf f x) (substrate r') by Wtac.
have gxr: inc (Vf f' x) (substrate r') by Wtac.
move: (CantorA is1 xsr) (CantorA is2 xsr) => isi1 isi2.
apply: (CantorD wor2 fxr gxr (orderIT (orderIS isi1) isi2)).
Qed.            

Lemma CantorF r r' x y y': worder r' ->
 inc y (substrate r') -> inc y' (substrate r') ->
 (seg_order r x) \Is  (seg_order r' y) ->
 (seg_order r x) \Is  (seg_order r' y') ->
 y = y'.
Proof.
move => wor2 ysr ysr' is1 is2.
exact:(CantorD  wor2 ysr ysr'  (orderIT (orderIS is1) is2)). 
Qed.


Lemma CantorG r r' x y: worder r -> worder r' ->
 (seg_order r x) \Is  (seg_order r' y) ->
 (forall x', glt r x' x -> exists2 y', glt r' y' y & 
   (seg_order r x') \Is  (seg_order r' y'))
 /\ (forall y', glt r' y' y -> exists2 x', glt r x' x & 
   (seg_order r x') \Is  (seg_order r' y')).
Proof.
move => wor1 wor2  [f fiso].
move: (proj1 wor1)  (proj1 wor2)=> or1 or2.
move: (fiso) =>[_ _ [bf sf tf]_].
move: (seg_order_wor x wor1) (seg_order_osr x (proj1 wor1)) => wor1x [_ sr1x].
move: (seg_order_wor y wor2) (seg_order_osr y (proj1 wor2)) => wor2y [_ sr2y].
rewrite sr1x in sf.
rewrite sr2y in tf.
have ff: function f by fct_tac.
suff aux x': glt r x' x ->
   (seg_order r x') \Is (seg_order r' (Vf f x')).
  split.
    move => x' lt1.
    have x'sf: inc x' (source f) by rewrite sf; apply/segmentP.
    have lt2 :glt r' (Vf f x') y by apply/segmentP; Wtac.
    exists (Vf f x'); [ exact | by apply: aux].
  move => y' lt3.
  have y'tf: inc y' (target f) by rewrite tf; apply/segmentP.
  move: (proj2 (proj2 bf) y' y'tf) =>[x' x'sf ->].
  have lt4: glt r x' x by  apply /segmentP; rewrite - sf.
  exists x' => //; exact: (aux _ lt4).
move => lt1.
have x'sf: inc x' (source f). by rewrite sf; apply/segmentP.
have lt2 :glt r' (Vf f x') y by apply/segmentP; Wtac.
have ii1: inc x' (substrate (seg_order r x)) by rewrite sr1x; apply/segmentP.
move: (CantorA fiso ii1); rewrite seg_order_trans // seg_order_trans //.
Qed.


Lemma CantorH r r' x x' y y': worder r -> worder r' ->
 inc x (substrate r) -> inc y (substrate r') ->
 inc x' (substrate r) -> inc y' (substrate r') ->
 (seg_order r x) \Is  (seg_order r' y) ->
 (seg_order r x') \Is (seg_order r' y') ->
 ((gle r x x' <-> gle r' y y' )/\ (glt r x x' <-> glt r' y y')).
Proof.
move => wor1 wor2 xsr ysr xsr' ysr' iso1 iso2.
move:(proj1 wor1)(proj1 wor2) => or1 or2.
have res1: x = x' -> y = y'.
  move => ea; rewrite -ea in iso2.
  exact: (CantorF wor2 ysr ysr' iso1 iso2).
have res2: y = y' -> x = x'.
  move => ea; rewrite -ea in iso2.
  exact: (CantorF wor1 xsr xsr' (orderIS iso1) (orderIS iso2)).
have res5: glt r x x' -> glt r' y y'.
  move => lt1.
  move: (proj1 (CantorG wor1 wor2  iso2) _ lt1) => [z lt2 is3].
  have zsr:= (arg1_sr (proj1 lt2)).
  move: (orderIT (orderIS is3) iso1) => iso3.
  by rewrite- (CantorF wor2 zsr  ysr is3 iso1).
have res4: glt r x' x -> glt r' y' y.
  move => lt1.
  move: (proj1 (CantorG wor1 wor2  iso1) _ lt1) => [z lt2 is3].
  have zsr:= (arg1_sr (proj1 lt2)).
  move: (orderIT (orderIS is3) iso2) => iso3.
  by rewrite  (CantorF wor2 ysr' zsr iso2 is3).
case: (equal_or_not x x') => ee.
  rewrite ee (res1 ee); split; [ by split => _; order_tac | by split; case].
case:(proj2 (worder_total wor1) x x' xsr xsr') => le1.
   by split; split => // _; move:(proj1 (res5 (conj le1 ee))).
move: (res4 (conj le1 (nesym ee))) => ltyy; move: (proj1 ltyy)=> leyy.
split; split => h.
- case:(not_le_gt or2 leyy (res5 (conj h ee))).
- case: ee; exact:(res2(proj44 or2 _ _ h leyy)).
- case:(not_le_gt or1 le1 h). 
- case:(not_le_gt or2 leyy h).
Qed.

Lemma CantorI r r' y: worder r -> worder r' ->
  inc y (substrate r') -> 
  (forall x, inc x (substrate r) -> ~ seg_order r x \Is seg_order r' y) ->
  (forall y',  glt r' y y' -> 
    forall x, inc x (substrate r) -> ~ seg_order r x \Is seg_order r' y')
  /\ forall x, inc x (substrate r) -> ~ seg_order r x \Is r'.
Proof.
move => wor1 wor2 ysr yp;split.
  move => y' ly1 x' xsr' is1.
  move: (proj2 (CantorG wor1 wor2 is1) y ly1) =>[x /proj1/arg1_sr xsr h].
  case: (yp x xsr h).
move => x xsr is1.
move:(orderIS is1) => [f ff]; move: (ff) =>[_ _  [[[fuf _] _]sf tf] _].
have lt1:  glt r (Vf f y) x.
   apply/segmentP; rewrite - (proj2 (seg_order_osr x (proj1 wor1))); Wtac.
case: (yp _ (arg1_sr (proj1 lt1))).
by move:(orderIS (CantorA ff ysr)); rewrite (seg_order_trans (proj1 wor1)).
Qed.

Definition Corder_le r r' := 
 (forall x, inc x (substrate r) -> exists2 y, inc y (substrate r') &
    seg_order r x \Is seg_order r' y). 
Definition Corder_lt r' r :=
  exists2 x, inc x (substrate r) & seg_order r x \Is r'.


Lemma CantorK r r': worder r -> worder r' ->
  Corder_le r r' -> Corder_le r' r -> r \Is r'.
Proof.
move => wor1 wor2 h1 h2.
move: (proj1 wor1) (proj1 wor2) => oe1 or2.
pose p x y := seg_order r x \Is seg_order r' y.
pose f x := (select (p x) (substrate r')).
have fp x: inc x (substrate r) -> p x (f x) /\ inc (f x) (substrate r').
  move => xsr.
  have sv: singl_val2 (inc^~ (substrate r')) (p x).
    move => u v /= usr pu vsr pv.
    exact:(CantorF wor2 usr vsr pu pv).
  by move: (select_pr (h1 x xsr) sv).
have ax: lf_axiom f (substrate r) (substrate r').
  by move => t /fp [].
have bp: bijection_prop (Lf f (substrate r) (substrate r')) 
     (substrate r) (substrate r').
  hnf; saw; apply: (lf_bijective ax).
    move => u v usr vsr sf.
    move: (fp u usr) (fp v vsr) =>[sa sb][sc sd]. rewrite - sf in sc.
    exact: (CantorF wor1 usr vsr (orderIS sa) (orderIS sc)).
  move => y ysr; move:(h2 _ ysr) => [x xsr /orderIS xp]; ex_tac.
  move: (fp x xsr) => [qa qb].
  exact: (CantorF wor2 ysr qb xp qa).
exists (Lf f (substrate r) (substrate r')); split => //.
hnf; aw; move => u v usr vsr; rewrite !LfV//.
move:(fp _ usr) (fp _ vsr) =>[sa sb][sc sd].
exact: (proj1 (CantorH wor1 wor2 usr sb vsr sd sa sc)).
Qed.

Lemma Cantor_not_le_aux r r'
   (p := fun y => exists2 x,
            inc x (substrate r) & seg_order r x \Is seg_order r' y):
  worder r' -> ~ Corder_le r' r ->
  exists a, [/\ inc a (substrate r'), ~ p a & forall b, glt r' b a -> p b].
Proof.
move => wor2 h2.
set E := Zo (substrate r') (fun y => ~ p y).
have ser: sub E (substrate r') by apply: Zo_S.
have neE: nonempty E.
  case: (all_exists_dichot1  p (substrate r')).
    move =>h3; case: h2 => y /h3 [x xst /orderIS xl]; ex_tac.
  by move => [x ha hb]; exists x; apply: Zo_i.
move: (worder_prop wor2 ser neE) =>[a /Zo_P [asr h] al].
exists a; split => //b ltab.
move:(arg1_sr (proj1 ltab)) => bsr.
ex_middle bad; have /al le2: inc b E by apply: Zo_i.
case: (not_le_gt (proj1 wor2) le2 ltab).
Qed.

Lemma CantorL r r': worder r -> worder r' ->
  Corder_le r r' -> ~ Corder_le r' r -> Corder_lt r r'.
Proof.
move => wor1 wor2 h1 h2.
move: (Cantor_not_le_aux wor2 h2) =>[a [asr ap al]].
pose pa x := seg_order r x \Is seg_order r' a.
case: (all_exists_dichot2 pa (substrate r)) => // hu.
have or2 := proj1 wor2.
move:(proj2(seg_order_osr a or2)) => sr1.
rewrite/Corder_lt; ex_tac; apply: orderIS.
apply: (CantorK wor1 (seg_order_wor a wor2));rewrite /Corder_le sr1.
  move => x xsr; move: (h1 _ xsr) =>[y ysr is1].
  case: (equal_or_not y a) => nay; first by case ap; rewrite - nay; hnf; ex_tac.
  case: (proj2 (worder_total wor2) _ _ ysr asr) => lay.
    have ys: inc y (segment r' a) by apply/segmentP.
    by ex_tac; rewrite seg_order_trans //.
  by case:(proj1 (CantorI wor1 wor2 asr hu) _ (conj lay (nesym nay)) _ xsr).
move => y ys.
have lya: glt r' y a by apply/segmentP.
move: (arg1_sr (proj1 lya)) => ysr.
move:(al y lya) => [x xsr /orderIS hx]; ex_tac;rewrite seg_order_trans //.
Qed.

    
Lemma CantorM r r': worder r -> worder r' ->
  ~ Corder_le r' r -> Corder_le r r'.
Proof.
move => wor1 wor2 h2; ex_middle h1.
move: (Cantor_not_le_aux wor1 h1) => [a [asr ap al]].
move: (Cantor_not_le_aux wor2 h2) => [b [bsr bp bl]].
suff: seg_order r a \Is  seg_order r' b.
  move => h; case: bp; ex_tac.
move: (seg_order_wor a wor1) (seg_order_wor b wor2) => sa sb.
move: (proj2(seg_order_osr a (proj1 wor1))) => sra.
move: (proj2(seg_order_osr b (proj1 wor2))) => srb.
move: (proj1 wor1) (proj1 wor2) => or1 or2.
apply: (CantorK sa sb).
  move => u; rewrite sra srb => /segmentP lt1.
  move:(arg1_sr (proj1 lt1)) => usr.
  move:(al _ lt1) =>[v vsr /orderIS is1].
  case: (total_order_pr1 (worder_total wor2) bsr vsr) =>  lt2.
  - pose pra z := seg_order r z \Is seg_order r' b.
    case: (all_exists_dichot2 pra (substrate r)) => // hu.
    by case:(proj1 (CantorI wor1 wor2 bsr hu) v lt2 u usr).
  - by move/segmentP: (lt2) => vsb; ex_tac; rewrite !seg_order_trans //.
  - by rewrite - lt2 in is1; case: bp; ex_tac.
move => v; rewrite sra srb => /segmentP lt2.
move:(bl _ lt2) =>[u usr /orderIS is1]; move:(arg1_sr (proj1 lt2)) => vsr.
case: (total_order_pr1 (worder_total wor1) asr usr) =>  lt1.
- pose pra z := seg_order r' z \Is seg_order r a.
  case: (all_exists_dichot2 pra (substrate r')) => // hu.
  by case: (proj1 (CantorI wor2 wor1 asr hu) u lt1 v vsr).
- by move/segmentP: (lt1) => usa; ex_tac; rewrite !seg_order_trans //.
- by rewrite - lt1 in is1; case: ap; ex_tac.
Qed.


Lemma CantorN r r'
  (Ha := r \Is r')(Hb:= Corder_lt r' r) (Hc:= Corder_lt r r') :
  worder r -> worder r' ->
  [/\  [\/  Ha, Hb | Hc],
       Ha -> ~Hb /\ ~Hc,
       Hb -> ~Ha /\ ~Hc &
       Hc -> ~Hb /\ ~Ha ].
Proof.
move => wor1 wor2.
have r1: Ha -> ~Hb.
   rewrite /Ha /Hb/Corder_lt => ha [x xsr hb].
   exact: (CantorB wor1 xsr (orderIT ha (orderIS hb))).
have r2: Ha -> ~Hc.
   rewrite /Ha /Hb/Corder_lt => ha [x xsr hb].
   exact: (CantorB wor2 xsr (orderIS (orderIT hb ha))). 
have r3: Hb -> ~Hc.
  have or2 := (proj1 wor2).
  move =>[x xsr is1] [y ysr /orderIS [f fiso]].
  have lt1: glt r' (Vf f x) y.
    move:(fiso) => [_ _ [[[ff _] _] sf tf] _].
    apply/segmentP; rewrite - (proj2 (seg_order_osr y (or2))); Wtac.
  move: (arg1_sr (proj1 lt1)) => fxsr.
  move: (CantorA fiso xsr);rewrite (seg_order_trans or2 lt1) => is2.
  exact:(CantorB wor2 fxsr (orderIT (orderIS is1) is2)).
split.
* case: (p_or_not_p (Corder_le r r')) => ha;
  case: (p_or_not_p (Corder_le r' r)) => hb.
  + constructor 1;exact:(CantorK wor1 wor2 ha hb).
  + constructor 3;exact: (CantorL wor1 wor2 ha hb).  
  + constructor 2;exact: (CantorL wor2 wor1 hb ha).  
  + case: ha; exact: (CantorM wor1 wor2 hb).
* by move => h; split; [ apply:r1 | apply: r2].
* by move => h; split => h'; [ case(r1 h') | case(r3 h) ].
* by move => h; split => h'; [ case (r3 h') | case(r2 h') ].
Qed.


Lemma CantorO r X: worder  r -> sub X (substrate r) ->
  r \Is induced_order r X \/ (Corder_lt(induced_order r X) r).
Proof.
move => wor Xsr.
case:(proj41(CantorN wor (induced_wor wor Xsr))) => h.
- by left.
- by right.
- move: h =>[x].
  rewrite (iorder_sr (proj1 wor) Xsr).
  rewrite /seg_order (iorder_trans _ (@sub_segment2 r X x)) => qa qb.
  have sb: sub (segment (induced_order r X) x) (segment r x).
    by move => t/segmentP/iorder_gltP [_ _ /segmentP].
  case:(CantorC wor (Xsr _ qa) sb (orderIS qb)).
Qed.


Theorem isomorphism_worder_alt r r': worder r -> worder r' ->
  let iso:= (fun u v f => 
    segmentp v (Imf f) /\ order_morphism f u v) in
  (exists! f,iso r r' f) \/ (exists! f, iso r' r f).
Proof.
move=> wor wor' iso.
set (E:= substrate r). 
set (E':= substrate r').
have or: order r by fprops.
have or': order r' by fprops.
move: (extension_osr E E').
set o1:=  (extension_order E E'); set o2:= opp_order o1.
move => [oe soe1]; move: (opp_osr oe) => [ooe osr].
have soe: sub_functions E E' = substrate o2 by ue.  
set (s:= (Zo (sub_functions E E')  (fun z  => exists2 u, 
    segmentp r u & iso (induced_order r u) r' z))).
have ssee: sub s (sub_functions E E') by rewrite /s; apply: Zo_S.  
have sse: sub s (substrate o1) by ue.
have ssoxee: sub s (substrate o2) by ue. 
have ins:inductive (induced_order o2 s).
  move=> X;rewrite (iorder_sr ooe ssoxee) => Xs;rewrite(iorder_trans _ Xs)=> pX.
  have Xse:sub X (sub_functions E E') by apply: (sub_trans Xs ssee).
  have Xsoe:sub X (substrate o2) by ue. 
  have alseg: forall x, inc x s -> segmentp r (source x).
    move=> x /Zo_hi [u ru [_ bb]]; move: bb =>  [_ _ [_ -> _] _].
    by rewrite iorder_sr //;apply: sub_segment1.
  have alsegr: forall x, inc x s -> segmentp r' (Imf x).
   by move=> x /Zo_hi  [u _ [sv _]].
  have Xso: sub X (substrate o1) by ue.
  move: pX => [_ ]; rewrite iorder_sr // => ppX.  
  have cov: forall u v x, inc u X -> inc v X ->  inc x (source u) -> 
    inc x (source v) ->  Vf u x = Vf v x.
    move=> u v x uX vX xsu xsv.
     move: (ppX _ _ uX vX); case => h; move: (iorder_gle1 h); 
        move/igraph_pP/ extension_orderP => [_ _ h0]; 
      [ | symmetry];apply: extends_sV => //.
  move:(sup_extension_order2 Xse cov)=> [x [lubx sx rgx gx]]. 
  move: lubx => /(lubP ooe Xsoe) [[xsoe xb] lub]; rewrite - soe in xsoe.
  suff xs: inc x s.
    exists x; split; first by rewrite iorder_sr //. 
    move=> y yX; move:  (Xs _ yX)=> ys.
    by apply /iorder_gle0P => //; apply: xb.
  have ssx: segmentp r (source x).
    rewrite sx; apply: setUf_segment.
    by hnf; aw;move=> a aX; rewrite LgV//;apply: alseg; apply: Xs.
  rewrite /s; apply: Zo_i=>//; exists (source  x) => //.
  have srgx: segmentp r' (Imf x). 
    rewrite rgx; apply: setUf_segment.
    by hnf;aw;move=> a aX; rewrite LgV//;apply: alsegr; apply: Xs.
  have sxsr: sub (source x) (substrate r) by move: ssx=> [].
  have srxs: sub (Imf x) (substrate r') by move: srgx => [].
  have xi: (forall a b,
      inc a (source x) ->  inc b (source x) ->
      (gle (induced_order r (source  x)) a b <->
      gle r' (Vf x a) (Vf x b))).
    move=> a b; rewrite sx => asX bsX.
    apply: (iff_trans(iorder_gle0P r asX bsX)).
    move: (setUf_hi asX)=> [u uX]. 
    move: (setUf_hi bsX)=> [v vX].
    rewrite Lgd in uX vX; rewrite !LgV// => bv au.
    have [w [wX asw bsw]] :exists z, 
     [/\ inc z X, inc a (source z) & inc b (source z)].
      move: (ppX _ _  uX vX) ; case => h; move: (iorder_gle1 h);
        move/igraph_pP/ extension_orderP => [_ _ ext];
          move: (extends_Ssource ext)=> sext.
          by move: (sext _ au) => ax; exists v.
        by move: (sext _ bv) => ax; exists u.
    rewrite - (extension_order_pr (xb _ wX) asw).
    rewrite - (extension_order_pr (xb _ wX) bsw). 
    move:(Xs  _ wX) => /Zo_hi [z [sz _  [_ [_ _ [_ sf _] ifz]]]]. 
    rewrite (iorder_sr or sz) in sf; rewrite - sf in ifz.
    split; last by move /(ifz _ _ asw bsw);apply:iorder_gle1.
    move => lab; apply /(ifz _ _ asw bsw);apply/(iorder_gleP ) => //.
  move: xsoe => /sfunctionsP [fx srcx tx].
  move:  (iorder_osr or srcx) => [pa pb].
  done.
move:(iorder_osr ooe ssoxee) => [oio sio].
move: (Zorn_lemma oio ins) => [f []]; rewrite iorder_sr // =>fis fmax.
move: (fis)  => /Zo_P [fee [x sx xiso]].
(* maybe f is the answer *) 
case: (equal_or_not x (substrate r)) => h.
  move: xiso; rewrite h iorder_substrate //; move=> xiso. 
  left; apply /unique_existence;split; first by exists f.
  move=> a b [s1 m1][s2 m2].
  by apply: (isomorphism_worder_unique (r:=r) (r':=r')).
(* first case is excluded; uniqueness is trivial *)   
right; apply /unique_existence;split; last first.
  move=> a b [s1 m1][s2 m2].
  by apply: (isomorphism_worder_unique (r:=r') (r':=r)) =>//.  
(* maybe the inverse of f is the answer *)
case: (equal_or_not (Imf f)  (substrate r'))=> h'.
  move: xiso => [_ xiso]; move: (order_morphism_fi xiso) => injf.
  set (g:= triple E' E (inverse_graph (graph f))).
  move: xiso=> [_ _ [ff sf tf] vf].
  have gf: sgraph (graph f) by fprops.
  have sf': source f = x by rewrite  sf iorder_sr //; apply: sub_segment1.
  have rgg: range (graph g) = x. 
    by rewrite /g; aw; rewrite igraph_range // domain_fg.
  have fg: function g.
    rewrite /g; apply: function_pr.
        split;fprops; move=> a b /=. 
        move/igraphP=> [pa J1g] /igraphP [pb J2g] sv.
        rewrite - sv in J2g; move: (injective_pr3 injf J1g J2g).
        by apply: pair_exten. 
      by move: rgg; rewrite /g; aw; move=> ->;move: sx=> [xe _]. 
    by rewrite igraph_domain // -(ImfE ff).
  exists g. 
  hnf; rewrite (ImfE fg) rgg /order_morphism;split => //.
  split => //; first by split => //;try solve [ rewrite /g; aw;trivial]. 
  move=> a b asg bsg.
  have fgp: (forall u, inc u (source g) ->
    (inc (Vf g u) (source f) /\ Vf f (Vf g u) = u)).
    move=> u usg;  move: (Vf_pr3 fg usg); rewrite {2} /g; aw.
    move/igraph_pP  => Jg; split; [ Wtac | symmetry;apply: (Vf_pr ff Jg)].
  move: (fgp _ asg)(fgp _ bsg)=> [W1s va][W2s vb]. 
  rewrite -{1} va -{1} vb.
  rewrite - (vf _ _ W1s W2s); split; first (by apply:iorder_gle1).
  move => lab; apply/iorder_gle0P => //; ue.
(*  Here f is not maximal, we construct an extension *)
case: (well_ordered_segment wor sx)=> aux; first by case:h.
move: aux=> [a asr xa].
move: xiso=> [st [_ _ [ff sf tf] isf]]. 
case: (well_ordered_segment wor' st)=> aux; first by case:h'.
move: aux=> [b vsr tb].
set (g:=extension f a b). 
have sfx: source f = x by rewrite sf iorder_sr // xa; apply: sub_segment.
have asf: ~ (inc a (source f)) by rewrite sfx xa; move;apply: not_in_segment.
have fg:function g by apply: extension_f. 
have tg: target g = E'.  
  rewrite/g /extension; aw; rewrite tf;  by apply: setU1_eq.
have sg: source g = segmentc r a.
  by rewrite /g/extension; aw; rewrite sfx xa; apply: segmentc_pr.
have sap t: sub (segmentc r t) (substrate r)  by apply: Zo_S. 
have rgg: (Imf g = segmentc r' b). 
  rewrite (ImfE fg) /g/extension; aw; rewrite - segmentc_pr // range_setU1.
  by rewrite - (ImfE ff) tb.
have gs: inc g s.
  rewrite /s; apply: Zo_i. 
     by apply/sfunctionsP;split => //; rewrite sg; apply: sap.   
  exists (segmentc r a).
      by apply: segmentc_segment.
  split; first by rewrite rgg; apply: segmentc_segment. 
  move: (iorder_osr or (sap a)) => []; rewrite - sg => pa pb.
  hnf;split => // u v; rewrite sg - segmentc_pr //.
  move => qa qb; apply: (iff_trans (iorder_gle0P r qa qb)).
  move: qa qb; rewrite - xa - sfx => /setU1_P ut /setU1_P vt.
  have p1: forall w, inc w (source f) -> glt r' (Vf f w) b.
    move=> w wsf.
    have: inc  (Vf f w) (Imf f) by Wtac.
    by rewrite tb; move/segmentP.
  have p2: forall w, inc w (source f) -> glt r w a.
    by move=> w; rewrite sfx xa; move/segmentP.
  case: ut => hu; [rewrite extension_Vf_in // | rewrite hu extension_Vf_out //].
    case:vt => hv;[rewrite extension_Vf_in // | rewrite hv extension_Vf_out //].
      move:(isf u v hu hv). move:(iff_sym(iorder_gle0P r hu hv)); rewrite sfx.
      move => qa qb; exact: (iff_trans qa qb).
     by move: (p1 _ hu)(p2 _ hu)=> [e1 _][e2 _].
  case:vt => hv;  [rewrite extension_Vf_in // | rewrite hv extension_Vf_out //].
    move: (p1 _ hv)(p2 _ hv)=> [e1 ne1][e2 ne2].
    split => h'';[ case: ne2 | case: ne1];order_tac.
  by split => _; order_tac.
(* We express maximality *)
have eqfg: g = f.
  have pa: inc g (sub_functions E E') by rewrite /g/extension; fprops.
  have pb: sub (graph f) (graph g) by rewrite corresp_g;fprops.
  have pc: sub (target f) (target g) by rewrite corresp_t ; fprops.
  apply: fmax; apply /iorder_gle0P => //; apply /igraph_pP.
  by apply /extension_orderP.
case: asf; rewrite -eqfg sg.
by apply: inc_bound_segmentc.
Qed.

  
End CantorCompare.
  

(* -------------------------------------------------------------------- *)

Module  ZermeloEq.
(* Equipotency, according to Zermelo *)


Definition zprod a := Zo (\Po (union a)) 
  (fun y=> forall x,  inc x a -> singletonp (y \cap x)). 

Definition zprod2 a b:= zprod (doubleton a b).

Lemma zprod2_P a b y:
  inc y (zprod2 a b) <->
  [/\ sub y (a \cup b), singletonp (y \cap a) & singletonp (y \cap b)].
Proof.
split.
  move => /Zo_P [] /setP_P pa pb;split => //; apply: pb; fprops.
move => [pa pb pc]; apply /Zo_P; split; first by apply /setP_P.
by move => x /set2_P; case => ->.
Qed.

Definition zpr x a := union  (x \cap a).
 
Lemma zprod2_pr1 a b x:
  inc x (zprod2 a b) -> 
  ((x \cap a = singleton (zpr x a)) /\
   (x \cap b = singleton (zpr x b))).
Proof. 
rewrite /zpr.
by move /zprod2_P => [pa [t ->] [s ->]]; rewrite ! setU_1.
Qed.

Lemma zprod2_pr0 a b x:
  inc x (zprod2 a b) ->
  [/\ inc (zpr x a) a, inc (zpr x b) b, inc (zpr x a) x & inc (zpr x b) x].
Proof.
move=>  xz; move: (zprod2_pr1 xz) => [pa pb].
have /setI2_P [sa sb] : (inc (zpr x a) (x \cap a)) by rewrite pa; fprops. 
have /setI2_P [sc sd] //: (inc (zpr x b) (x \cap b)) by rewrite pb; fprops. 
Qed.

Lemma zprod2_pr0aa a b x:
  inc x (zprod2 a b) -> inc (zpr x a) a.
Proof. by move=> xz; case: (zprod2_pr0 xz).  Qed.

Lemma zprod2_pr0ax a b x:
  inc x (zprod2 a b) -> inc (zpr x a) x.
Proof. by move=> xz; move: (zprod2_pr0 xz) => []. Qed.

Lemma zprod2_pr0bb a b x:
  inc x (zprod2 a b) -> inc (zpr x b) b.
Proof. by move=> xz; move: (zprod2_pr0 xz) => []. Qed.

Lemma zprod2_pr0bx a b x:
  inc x (zprod2 a b) -> inc (zpr x b) x.
Proof. by move=> xz; move: (zprod2_pr0 xz) => []. Qed.

Lemma zprod2_pr1a a b x z:
  inc x (zprod2 a b) -> 
  inc z a -> inc z x -> z = zpr x a.
Proof. 
move=> xz za zb; apply/set1_P;move: (zprod2_pr1 xz)=> [<- _]; fprops.
Qed.

Lemma zprod2_pr1b a b x z:
  inc x (zprod2 a b) -> 
  inc z b -> inc z x -> z = zpr x b.
Proof. 
move=>  xz zb zx;  apply/set1_P; move: (zprod2_pr1 xz)=> [_ <-]; fprops.
Qed.

Lemma zprod2_pr2 a b x:
  inc x (zprod2 a b) -> x = doubleton (zpr x a) (zpr x b).
Proof. 
move=> yz; set_extens z; aw.
  move: (yz) => /zprod2_P [pa pb pc]. 
  move=> xy; move: (pa _ xy);case /setU2_P => h.
   rewrite (zprod2_pr1a yz h xy); fprops.
   rewrite (zprod2_pr1b yz h xy); fprops.
by move: (zprod2_pr0ax yz) (zprod2_pr0bx yz) => pa pb;case /set2_P=> ->.
Qed.

Lemma intersection_singletonP a b c:
  (a \cap (singleton b) = singleton c) <->
  (inc c a /\ c = b).
Proof. 
split. 
  move=>  iis; move:(set1_1 c); rewrite -iis => /setI2_P.
  by move => [pa] /set1_P. 
move=> [pa <-]; apply: set1_pr; first by fprops.
by move => t /setI2_P [_] /set1_P.
Qed.

Lemma is_singleton_int a b c:
  inc c a -> inc c b -> (forall u, inc u a-> inc u b -> u = c) ->
  singletonp (a \cap b).
Proof. 
move=> ca cb h;exists c; apply: set1_pr; first by fprops.
by move => t /setI2_P [pa pb]; apply : h.
Qed.

Lemma zprod_singleton M r: ~ inc r M ->
  let N := zprod2 M (singleton r) in
    ( (forall u, inc u M -> inc (doubleton u r) N) /\
      (forall x, inc x N -> exists2 u, inc u M & x = doubleton u r)).
Proof.
move=> nrM N; split.
  move=> u uM; apply /zprod2_P;split => //. 
      move=> t /set2_P; case => ->; apply /setU2_P; [left | right]; fprops.
    exists u; apply: set1_pr; first by fprops.
    by move=> t /setI2_P [] /set2_P; case => // ->.
  exists r; apply /intersection_singletonP;fprops.
move=> x xN; move: (zprod2_pr0 xN) => [pa /set1_P <- _ _].
by ex_tac; exact: (zprod2_pr2 xN).
Qed.

Definition zmap f a b := sub f (zprod2 a b) /\ 
  (forall x, inc x (a \cup b)-> exists !z, inc z f /\ inc x z).

Definition ziequivalent a b := disjoint a b /\ exists f, zmap f a b.


Lemma zmap_symm f a b: zmap f a b -> zmap f b a.
Proof. rewrite /zmap setU2_C /zprod2 set2_C //. Qed.

Lemma zequiv_symm a b: ziequivalent a b -> ziequivalent b a.
Proof. 
move => []; rewrite /disjoint setI2_C; move=> h [f zf].
by move: (zmap_symm zf) => zf1; split => //; exists f.
Qed.

Lemma zmap_example1  a b: a <> b ->
  let A := singleton a in
    let B := singleton b in
    zmap (singleton (doubleton a b)) A B.
Proof. 
move=> nab A B; rewrite /A/B.
move: (setU2_11 a b); set (u := doubleton a b) => aux.
split.  
  by move=> t /set1_P ->; apply /zprod2_P; rewrite  aux /u;split => //;
   [exists a | exists b]; apply:set1_pr; try (apply /setI2_P;split;fprops);
     move => z /setI2_P [_] /set1_P.
rewrite aux; move=> x xu; exists u; split => //; first split; fprops.
by move => t [] /set1_P.
Qed.

Lemma zmap_example2 a b c d: let A := doubleton a b in
  let B := doubleton c d in
    disjoint A B -> a <> b -> c <> d ->
    zmap (doubleton (doubleton a c) (doubleton b d)) A B.
Proof. 
move=>  A B dab nab ncd.
move: dab; rewrite /disjoint /A/B=> ie.
have nac: a <> c by  move => ac; empty_tac1 a; rewrite ac; fprops.
have nad: a <> d by  move => ac; empty_tac1 a;rewrite ac; fprops.  
have nbc: b <> c by  move => ac; empty_tac1 b;rewrite ac; fprops.
have nbd: b <> d by  move => ac; empty_tac1 b;rewrite ac; fprops.  
have Hx: forall x y z,  y <> z ->
    singletonp (intersection2 (doubleton x y) (doubleton x z)).
  move=> x y z yz; exists x; apply: set1_pr; first by fprops.
  move => t /setI2_P []/set2_P; case => // -> /set2_P; case => //.
split.
  move=> t t1; apply / zprod2_P; case /set2_P: t1 =>  ->; split => //; 
    try (move => w /set2_P; case => ->; fprops).
   - by apply: Hx; apply: nesym.
   - by rewrite (set2_C a c); apply: Hx.
   - by rewrite (set2_C a b); apply: Hx; apply:nesym.
   - by rewrite set2_C (set2_C c d); apply: Hx.
have ->: ((doubleton a b) \cup (doubleton c d))  =
    (doubleton a c) \cup (doubleton b d). 
   set_extens t => /setU2_P; case => /set2_P; case => ->; fprops. 
move => x xu; apply /unique_existence; split.
   case /setU2_P: xu => h;
    [ exists  (doubleton a c) | exists  (doubleton b d) ]; split;fprops.
move=> u v  [] /set2_P pa qa [] /set2_P pb qb; move: qa qb.
have aux: inc x (doubleton a c) -> inc x (doubleton b d) -> False. 
  by case /set2_P => ->; case /set2_P => //; apply:nesym.
by case: pa => ->; case: pb =>-> // qc qd; case: aux.
Qed.

Lemma zequiv_example1 a b: a <> b ->
  ziequivalent (singleton a) (singleton b).
Proof. 
move=> ab; split; first by  apply: disjoint_pr => u /set1_P -> /set1_P.
exists (singleton (doubleton a b)); apply: (zmap_example1 ab).
Qed.

Lemma zequiv_example2  a b c d: let A := doubleton a b in
  let B := doubleton c d in
    disjoint A B -> a <> b -> c <> d ->
    ziequivalent A B.
Proof.
move=> A B dAB nab ncd; split => //. 
exists (doubleton (doubleton a c) (doubleton b d)); by apply: zmap_example2.
Qed.

Definition zbijective F a b :=
  [/\ (forall x, inc x a -> inc (F x) b) ,
      (forall x x', inc x a -> inc x' a -> F x = F x' -> x = x') &
      (forall y, inc y b -> exists2 x, inc x a & y =  F x)].

Lemma zmap_example3 F a b: disjoint a b -> zbijective F a b ->
  ziequivalent a b.
Proof.
move=> dab [pa pb pc]; split => //. 
set (f := Zo (\Po (union2 a b)) (fun z => exists2 x, inc x a & 
    z = doubleton x (F x))).
red in dab.
exists f; split. 
  move=> t => /Zo_P  [] /setP_P tu [x xa td]; apply /zprod2_P.
  move: (pa _ xa)=> fb; split => //.
    apply: (@is_singleton_int _ _ x) => //; first by rewrite td;fprops.
    rewrite td => u;case/set2_P =>// qa qb; empty_tac1 u. 
    apply /setI2_P;split => //;ue.
  apply: (@is_singleton_int _ _  (F x)) => //; first by rewrite td;fprops.
  rewrite td => u; case /set2_P =>// qa qb; empty_tac1 u. 
  apply /setI2_P;split => //;ue.
move=> x; aw => xu; apply /unique_existence; split.
  case /setU2_P: xu => xu. 
    exists (doubleton x (F x)); split; last by fprops.
    apply: Zo_i; last by ex_tac.
    apply /setP_P;move => t;case /set2_P=> ->; [ fprops | apply /setU2_P].
    by right; apply: pa.
  move: (pc _ xu)=> [z za Fz]; exists (doubleton z x);split;fprops.
  apply: Zo_i; first by apply /setP_P;move=> t; case /set2_P=> ->; fprops.
  ex_tac; ue.
move=> u v [uf xz] [yf xy].
move: uf yf => /Zo_P [] /setP_P uu [z za zu] /Zo_P [] /setP_P vy [w wa vw].
move: xz xy;rewrite zu vw; case /set2_P => xpa; case  /set2_P=> xpb.
- by rewrite -xpa -xpb.
- by empty_tac1 x; apply /setI2_P;split => //; ue.
- by empty_tac1 x;  apply /setI2_P; split => //; ue; rewrite xpa; apply: pa.
- by rewrite xpa in xpb; rewrite (pb _ _ za wa xpb).
Qed.


Lemma zmap_pr1 f a b: zmap f a b -> union f = a \cup b.
Proof. 
move=>  [pa pb]; set_extens t.
  move /setU_P => [y ty yf]; move: (pa _ yf) => /zprod2_P.
   by move=> [yu _ _]; apply: yu.
move => tu; move: (pb _ tu) => [z [[zf xz] _]]; union_tac.
Qed.

Definition zmap_aux f x := select  (fun z => inc x z) f.

Lemma zmap_aux_pr1 f a b x:
  zmap f a b -> inc x (a \cup b) ->
  (inc (zmap_aux f x) f /\ inc x (zmap_aux f x)).
Proof.
move=> [pa pb] xu; move: (pb _ xu) => [u [[ta tb] pd]].
have h: singl_val2 (inc^~ f) (fun z => inc x z).
  by move => t y sa sb sc sd; rewrite -(pd _ (conj sa sb)) -(pd _ (conj sc sd)).
rewrite /zmap_aux - (select_uniq h ta tb);split => //.
Qed.

Lemma zmap_aux_pr2 f a b x y:
  zmap f a b -> inc x (a \cup b) -> inc y f -> inc x y ->
  y = (zmap_aux f x).
Proof. 
move =>  zm xu yf xy;move: (zmap_aux_pr1 zm xu) => [pa pb]. 
move: zm=> [_ pc]; move: (pc _ xu) => [z [zx unq]]. 
by rewrite - (unq _ (conj yf xy)) (unq _ (conj pa pb)).
Qed.

Lemma zmap_aux_pr3a f a b x y:
  zmap f a b -> inc x f -> inc y f ->  zpr x a = zpr y a  ->
  x = y.
Proof. 
move=> zm xf yf szp; move: (zm) => [pa pb].
have zxu: (inc  (zpr x a) (union2 a b)).
  by apply: setU2_1; apply: (zprod2_pr0aa (pa _ xf)).  
have zyu: (inc  (zpr y a) (union2 a b)) by ue.
rewrite (zmap_aux_pr2 zm zxu xf (zprod2_pr0ax (pa _ xf))).
by rewrite (zmap_aux_pr2 zm zyu yf (zprod2_pr0ax (pa _ yf))) szp.
Qed.

Lemma zmap_aux_pr3b f a b x y:
  zmap f a b -> inc x f -> inc y f ->  zpr x b = zpr y b ->
  x = y.
Proof. move=> zm; apply: (zmap_aux_pr3a (zmap_symm zm)). Qed.

Definition zmap_val f a x:= zpr (zmap_aux f x) a.

Lemma zmap_val_pr1a f a b x: zmap f a b ->  inc x (a \cup b) -> 
  inc (zmap_val f a x) a.
Proof. 
move=> zm xu;move: (zmap_aux_pr1 zm xu) => [pc pd]. 
move: (zm) => [pa pb]; apply: (zprod2_pr0aa (pa _ pc)).
Qed.

Lemma zmap_val_pr1b  f a b x: zmap f a b ->  inc x (a \cup b) -> 
  inc (zmap_val f b x) b.
Proof. 
move => zmf xu; move: (zmap_aux_pr1 zmf xu) => [zf xz].
move: zmf => [pa pb];move: (pa _ zf); apply: zprod2_pr0bb.
Qed.

Lemma zmap_val_pr2a  f a b x: zmap f a b ->  inc x a ->
  (zmap_val f a x) = x.
Proof. 
move => cx xa.
have  xu: (inc x (union2 a b)) by apply: setU2_1.  
move : (zmap_aux_pr1 cx xu) => [zf xz]; move: cx => [pa pb].
symmetry; apply: (zprod2_pr1a  (pa _ zf) xa xz).
Qed.

Lemma zmap_val_pr2b  f a b x: zmap f a b ->  inc x b ->
  (zmap_val f b x) = x.
Proof. 
move => cx xb.
have  xu: (inc x (union2 a b)) by apply: setU2_2.  
move : (zmap_aux_pr1 cx xu) => [zf xz]; move: cx => [pa pb].
symmetry; apply: (zprod2_pr1b  (pa _ zf) xb xz).
Qed.

Lemma zmap_val_pr3a  f a b x: zmap f a b ->  inc x a ->
  (zmap_val f a (zmap_val f b x)) = x.
Proof. 
move=> zm xa.
have xu: inc x (union2 a b) by apply: setU2_1. 
move: (zmap_aux_pr1 zm xu) => [zf xz].
move: (zm) => [pa pb]; move: (pa _ zf) => xx.
move:  (zprod2_pr1 xx) => [pc pd].
set (t := zmap_val f b x); set y := zmap_aux f x.
have: inc t (y \cap b) by rewrite pd; fprops.
move /setI2_P => [ta1 ta2].
have tab: (inc t (a \cup b)) by apply: setU2_2.
suff: y = zmap_aux f t.
   rewrite /zmap_val; move => <-;symmetry; apply: (zprod2_pr1a (pa _ zf) xa xz).
apply: (zmap_aux_pr2 zm tab zf ta1).
Qed.

Lemma zmap_val_pr3b f a b x: zmap f a b ->  inc x b ->
  (zmap_val f b (zmap_val f a x)) = x.
Proof.  
move =>  zm; have: (zmap f b a) by apply: zmap_symm.  
apply: zmap_val_pr3a.
Qed.

Lemma zmap_bijective f a b: zmap f a b -> 
  zbijective (zmap_val f b) a b.
Proof.
move=> zm; rewrite /zbijective; split => //. 
    move=> x xa; apply: (zmap_val_pr1b zm (setU2_1 b xa)).
  move=> x x' xa x'a sv;  move: (f_equal (zmap_val f a) sv). 
  rewrite zmap_val_pr3a //  zmap_val_pr3a //.
move=> y yb; exists ( zmap_val f a y).
  by apply: (zmap_val_pr1a zm); apply /setU2_2.
by rewrite zmap_val_pr3b.
Qed.

Lemma zmap_setP a b: exists s,
  forall f, zmap f a b <-> inc f s.
Proof.
exists (Zo (\Po (zprod2 a b)) (fun z => zmap z a b)).
move=> f; split; last by move =>  /Zo_P [].
by  move => h; apply /Zo_P;split => //; apply /setP_P;move: h => [].
Qed.

Lemma sub_disjoint a b a' b':
  disjoint a b -> sub a' a -> sub b' b -> disjoint a' b'.
Proof. 
move=>  di sa sb; apply: disjoint_pr => u ua ub.
red in di; empty_tac1 u; saw.
Qed. 

Lemma zmap_sub f a b a': zmap f a b -> sub a' a ->
  exists f' b', [/\ sub f' f, sub b' b & zmap f' a' b'].
Proof. 
move=> zm saa.
move: (zm) => [pa pb].
set (f' := Zo f (fun z => inc (zpr z a) a')).
set (b':= Zo b (fun z => exists2 x, inc x f' & z = zpr x b)).
have sf: sub f' f by apply: Zo_S.
have sb: sub b' b by apply: Zo_S.
exists f'; exists b'; split => //. 
have pc:  (forall y, inc y f' ->  y = doubleton (zpr y a) (zpr y b)).
   by move=> y yf'; apply: zprod2_pr2; apply: pa; apply: sf.
split.
  move => x xf'.
  have ha: inc x (zprod2 a b) by apply: pa; apply: sf.
  have hb: (inc (zpr x a) a') by  move: xf' => /Zo_P [].
  have hc: (inc (zpr x b) b') by apply: Zo_i; [apply:(zprod2_pr0bb ha)| ex_tac].
  move: (zprod2_pr1 ha) => [pd pe].
  apply /zprod2_P;split => //.
      rewrite (pc _ xf');  move=> t;case /set2_P => ->; fprops.
    apply: (@is_singleton_int _ _ (zpr x a)) => //.
      apply: (@setI2_1 _ a); rewrite pd; fprops.
    move=> u ux ua'. 
    have : (inc u (x \cap a)) by fprops.
    by rewrite pd => /set1_P.
  apply: (@is_singleton_int _ _ (zpr x b)) => //.
    apply: (@setI2_1 _ b); rewrite pe; fprops.
  move=> u ux ua'. 
  have : (inc u (x \cap b)) by fprops.
  by rewrite pe => /set1_P.
move=> x xu.
have xu': (inc x (a \cup b)) by  move: xu; case /setU2_P => xs; fprops.
move: (zmap_aux_pr1 zm xu') => [pd pe]; exists (zmap_aux f x); split. 
    split => //; apply: Zo_i => //.
  move: xu; case /setU2_P => xs. 
    by move: (zmap_val_pr2a zm (saa _ xs)); rewrite /zmap_val; move => ->.
  move: xs => /Zo_P [xb [z zf' xv]].
  move: zf' => /Zo_P  [pf pg].
  have  <- //: (z = zmap_aux f x).  
  apply: (zmap_aux_pr2 zm xu' pf); rewrite xv; apply: (zprod2_pr0bx (pa _ pf)).
move=> u [uf' ux]; move: (pb _ xu') => [z [zv zu]].
by rewrite - (zu _ (conj pd pe)) (zu _ (conj (sf _ uf') ux)).
Qed.

Lemma zequiv_sub a b a': ziequivalent a b -> sub a' a ->
  exists b',  (sub b' b /\ ziequivalent a' b').
Proof.
move=>  [pa [f zm]] a'a.
move:  (zmap_sub zm a'a) => [f' [b' [pb pc pd]]]; exists b';split => //.
split; [ apply: (sub_disjoint pa a'a pc) |  by exists f'].
Qed.

Lemma zmap_transitive a b c: disjoint a c ->
  ziequivalent a b -> ziequivalent b c -> ziequivalent a c.
Proof. 
move=> dac [dab [f zmf]] [dbc [g zmg]].
move: (zmap_bijective zmf) (zmap_bijective zmg) => [pa pb pc][pd pe pf].
set (f1 := zmap_val f b);  set (f2 := zmap_val g c). 
set (h := fun x => f2 (f1 x)).
suff : (zbijective h a c) by apply: (zmap_example3 dac).
split => //; first by move=> x xa; apply: pd; apply: pa.
  fprops.
move=> y yc; move: (pf _ yc) => [x xb xb1].
by move: (pc _ xb) => [u ua uv]; ex_tac; rewrite xb1 uv.
Qed.

Lemma disjointness M: exists N,
  sub N M /\ ~ inc N M.
Proof. 
set (N := Zo M (fun x => ~ (inc x x))).
have NM: (sub N M) by apply: Zo_S.
exists N; split => // nm.
have aux: (~ (inc N N))by move=> bad; move: (bad) => /Zo_P [].
by apply: (aux); apply: Zo_i.
Qed.

Lemma disjointness1  M N: exists r,
  let M1 := zprod2 M (singleton r) in 
   [/\ ~ (inc r M) , disjoint M M1 & disjoint N M1].
Proof. 
move: (disjointness (M \cup (union (M \cup N)))) => [K [pa pb]].
have : (~ (inc K (union (M \cup N)))) by  dneg k; fprops.  
have kM: (~ inc K M) by dneg km; fprops.
have d1: (disjoint (union2 M N) (zprod2 M (singleton K))).
  apply: disjoint_pr => u uu us.
  move: (zprod_singleton kM) => [pc pd]; move: (pd _ us) => [v vM ud]. 
  case: pb; apply: setU2_2; apply /setU_P; exists u => //; rewrite ud; fprops.
move=> nku;exists K;split => //;apply: disjoint_pr => u um  aux; empty_tac1 u.
Qed.

Lemma zmap_example4 M r:
  let N := zprod2 M (singleton r) in 
    ~ (inc r M) -> disjoint M N ->
    ziequivalent M N.
Proof.
move=> N h1 h2. 
move: (zprod_singleton h1) => [pa pb].
suff : (zbijective (fun x => doubleton x r) M N) by apply: (zmap_example3 h2).
split => //.
move=> x x' xM xM' sf.
have : (inc x (doubleton x r)) by fprops.
rewrite sf;case /set2_P => // aux;case: h1; ue.
Qed.

Lemma zequiv_example4 M N: exists M',
  disjoint N M' /\ ziequivalent M M'.
Proof. 
move: (disjointness1 M N) => [r [a pa pb]].
by exists (zprod2 M (singleton r)); split => //; apply: zmap_example4.
Qed.


Lemma zequiv_empty M: ziequivalent M emptyset -> M = emptyset.
Proof.
move=>  [_ [f zm]]; apply /set0_P => x xM.
have xu: (inc x (M \cup emptyset)) by  rewrite setU2_0.
by move: (in_set0 (zmap_val_pr1b zm xu)). 
Qed.

Lemma zequiv_no_graph M: nonempty M ->
  ~ (exists S, forall M',  ziequivalent M M' -> inc M' S).
Proof. 
move=> nM [S hs].
move: (zequiv_example4 M (union S)) => [M' [ds emm']].
move: (hs _ emm') => ms'.
case: (emptyset_dichot M') => me.
  rewrite me in emm'; move: (zequiv_empty emm') => em.
  by move: nM; rewrite em; case /nonemptyP.
move: me => [x xm]; empty_tac1 x; union_tac.  
Qed.

Definition zequiv  M N := exists2 R, ziequivalent M R & ziequivalent N R.

Lemma zequiv_reflexive M: zequiv M M.
Proof.  by move: (zequiv_example4 M M) =>[N [_ nv]]; exists N. Qed.

Lemma zequiv_symmetric M N:
   zequiv  M N -> zequiv  N M.
Proof. by move=>  [f [fa fb]]; exists f. Qed.

Lemma zequiv_transitive M N P:
   zequiv  M N -> zequiv N  P -> zequiv M P.
Proof. 
move=>  [f fa fb] [g ga gb].
move:  (zequiv_example4 f (g \cup (P \cup (M \cup N)))) => [h [hd he]].
red in hd.
exists h => //.
  have d1: (disjoint M h) by apply: disjoint_pr => u uM uh; empty_tac1 u; aw.
  exact: (zmap_transitive d1 fa he).
have d2: (disjoint N h) by apply: disjoint_pr => u uM uh; empty_tac1 u; aw. 
move: (zmap_transitive d2 fb he) => Nh.
have d3: (disjoint g h) by apply: disjoint_pr => u uM uh; empty_tac1 u; aw.
move: (zmap_transitive d3 (zequiv_symm ga) Nh) => gh.
have d4: (disjoint P h) by apply: disjoint_pr => u uM uh; empty_tac1 u; aw.
exact (zmap_transitive d4 gb gh). 
Qed.

Lemma zequiv_equipotent M N: zequiv M N <->  M \Eq N.
Proof.
have Ha: forall a b, ziequivalent a b -> a \Eq b.
  move => a b [dab [f zf]].
  exists (Lf (zmap_val f b) a b); saw; apply:lf_bijective.
  - move => t ta; exact:(zmap_val_pr1b zf (setU2_1 b ta)). 
  - move => u v ua va => zz.
    by rewrite - (zmap_val_pr3a zf ua)  - (zmap_val_pr3a zf va) zz.
  - move => y yb; rewrite - (zmap_val_pr3b zf yb). 
    have va:=(zmap_val_pr1a zf (setU2_2 a yb)); ex_tac.
have Hb: forall x y, disjoint x y -> x \Eq y -> ziequivalent x y.
  move => x y dxy [f [[[ff ijf] [_ sjf]] sf tf]].
  suff: zbijective (Vf f) x y by apply:zmap_example3.
  split. 
  - move => t tx; Wtac.
  - by rewrite - sf.
  - by rewrite - sf - tf.
split.
  move => [x xA xB]; exact: (EqT (Ha _ _ xA) (EqS (Ha _ _ xB))).
move => MN. move: (zequiv_example4 M N) => [M' [h1 h2]].
exists M' => //; apply:(Hb _ _ h1); exact: (EqT (EqS MN) (Ha _ _ h2)).
Qed.

End ZermeloEq.


