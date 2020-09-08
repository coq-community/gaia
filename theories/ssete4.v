(** * Theory of Sets : Exercises sections 4 
  Copyright INRIA (2009-2013 2018) Apics/Marelle Team (Jose Grimm). 
*)
(* $Id: ssete4.v,v 1.5 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp
Require Import ssreflect ssrfun ssrbool eqtype ssrnat.  

Require Export  ssete3.


Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Exercise4.

(** Exercise 4.1. is in file ssete3 *)

(** Exercise 4.2. A set is finite iff  every
non-empty subset of the powerset  has a maximal element (with respect to
inclusion).  *)

Definition meet A B := nonempty (A \cap B).

Lemma finite_is_maximal_inclusion x:
  finite_set x <->
  (forall y, sub y (\Po x) -> nonempty y -> exists2 z, 
     inc z y & forall t, inc t y -> sub z t -> z = t).
Proof.
split.
  move: x; apply: finite_set_induction0.
    move=> y yp0 [t ty].
    have yp1: forall v, inc v y -> v = emptyset.
      by move=> v vy; move: (yp0 _ vy); rewrite setP_0 => /set1_P.
    by ex_tac => v vy tv; rewrite (yp1 _ ty) (yp1 _ vy).
  move=> a b hrec nba y yp yne.
  set Z:= Zo y (fun z => inc b z); case: (emptyset_dichot Z) => ze.
    have yp1: sub y (\Po a).
      move => t ty; move: (yp _ ty) => /setP_P ta; apply /setP_P => u ut.
      move: (ta _ ut); case /setU1_P => // ub;empty_tac1 t;apply: Zo_i =>//; ue.
    by apply: hrec.
    set T:= fun_image Z (intersection2 a).
    have Tp: sub T (\Po a).
      move => t /funI_P  [z zZ ->]; apply /setP_P;apply: subsetI2l.
    have neT:nonempty T.
      move: ze => [z zZ]; exists (a \cap z); apply /funI_P; ex_tac.
  move: (hrec _ Tp neT)=> [z zT zm].
  move: zT =>  /funI_P[u uZ iau]. 
  move: uZ => /Zo_P [uy bu].
  ex_tac; move=> t ty ut. 
  have bt: inc b t by apply: ut.
  have tz: inc t Z by apply: Zo_i => //.
  have it: inc (a \cap t) T by apply /funI_P; ex_tac.
  have it1: sub z (a \cap t).
    rewrite iau => w /setI2_P [p1 p2]; apply /setI2_P;split;fprops.
  move: (zm _ it it1) => zi.
  apply: extensionality => // v vt; move: (yp _ ty). 
    move /setP_P => tt;move:(tt _ vt); case /setU1_P; last by move => ->.
  by move => va;apply:  (@setI2_2 a);rewrite-  iau zi; apply:setI2_i.
move=> h.
set F := (finite_subsets x). 
have p1:sub F (\Po x) by apply: Zo_S.
have p2: nonempty F.
  exists emptyset; apply:Zo_i; [ apply: setP_0i| apply:emptyset_finite].
move: (h _ p1 p2) => [z /Zo_P [] /setP_P zpo zf zp].
case: (emptyset_dichot (x -s z)) => ce.
  have -> //: x = z by  apply:extensionality => //; apply:empty_setC.
move: ce => [y] /setC_P [yx nyz].
set (t:= z +s1 y).
have tF: inc t F. 
  by  apply:Zo_i; [apply /setP_P; apply: setU1_sub | apply:setU1_finite].
have zt: sub z t by move=> u uz; rewrite /t; fprops.
move: (zp _ tF zt) => tz; case: nyz; rewrite tz /t; fprops.
Qed.

(** ---- Exercise 4.3 is in file ssete3 *)

(** Exercise 4.4. Assume that [C] is a subset of [E x E] that contains a
pair [(x , y) ] if and only if it does not contain [(y, x)]. 
We can re-order the elements of [E] as [(x(1), x(2), ..., x(n))] so that
[(x(i),x(i+1))] is in [C].
 *)


Lemma Exercise4_4 n E C:
  natp n -> cardinal E = n -> sub C (coarse E) -> 
  (forall x y, inc x E -> inc y E -> x <> y -> 
    (exactly_one (inc (J x y) C) (inc (J y x) C))) ->
    exists2 f,  bijection_prop f (Nint1c n) E &
      (forall i, \1c <=c i -> i <c n -> 
        inc (J (Vf f i) (Vf f (csucc i))) C). 
Proof.
move=> nN cn _; move: n nN E cn C.
apply: Nat_induction1.
move=> n nN hrec E nE C cp.
case: (emptyset_dichot E) => Ee.
  rewrite  -nE Ee cardinal_set0. 
  have  ->: (Nint1c \0c) = emptyset.
    apply /set0_P => t /(Nint1cP NS0)  [pa pb].
    case: (clt0 (conj pb pa)).
  exists (identity emptyset); [by apply: identity_bp | by move => i _ /clt0].
move: Ee => [a aE].
set E1 := E -s1 a.
have  s1:sub (singleton a) E by apply: set1_sub.
set Z1:= Zo E1 (fun z => inc (J z a) C).
set Z2:= Zo E1 (fun z => inc (J a z) C).
have Z1E1: sub Z1 E1 by apply: Zo_S.
have sE1E: sub E1 E by apply: sub_setC.
have Z1E: sub Z1 E by apply: sub_trans  sE1E.
have Z2E: sub Z2 E by apply: sub_trans sE1E=>//; apply: Zo_S.
have Z2c: Z2 = E1 -s Z1.
  set_extens t. 
    move /Zo_P => [ta tb]; apply /setC_P; split => //; move /Zo_P => [_ tc].
    move /setC_P: ta => [te ] /set1_P tna.
    by case: (proj2 (cp _ _ te aE tna)). 
  move => /setC_P [te h]; apply /Zo_P;split => //.
  move /setC_P: (te) => [te1 ] /set1_P tna.
  case: (proj1 (cp _ _ te1 aE tna)) => // pa. 
  case: h; apply :Zo_i => //.
move: (cardinal_setC s1); rewrite /cdiff cardinal_set1 -/E1 csumC.
move: (cardinal_setC Z1E1); rewrite  /cdiff  -Z2c nE; move => <-.
set n1:= cardinal Z1; set n2:= cardinal Z2.
rewrite - (csucc_pr4 (CS_sum2 n1 n2))=> rel1.
have n1n2N: natp (n1 +c n2).
  by move:nN; rewrite - rel1 => h;move:(NS_nsucc (CS_sum2 n1 n2) h).
move: (cltS n1n2N); rewrite rel1 => aux2.
have aux3: n1 <=c (n1 +c n2) by apply: csum_M0le; rewrite /n1; fprops.
have aux4: n2 <=c (n1 +c n2) by apply: csum_Mle0; rewrite /n2;fprops.
have ltn1n:= cle_ltT aux3 aux2.
have ltn2n:= cle_ltT aux4 aux2.  
move:(NS_lt_nat ltn1n nN) (NS_lt_nat ltn2n nN)=> n1N n2N.
have c1p: (forall x y, inc x Z1 -> inc y Z1 -> x <> y ->
  exactly_one (inc (J x y) C) (inc (J y x) C)).
   move=> x y xz1 yz1 xy; apply: (cp _ _ (Z1E _ xz1)(Z1E _ yz1) xy).
have c2p: (forall x y, inc x Z2 -> inc y Z2 -> x <> y ->
    exactly_one (inc (J x y) C) (inc (J y x) C)).
 by move=> x y xz1 yz1 xy; apply: (cp _ _ (Z2E _ xz1)(Z2E _ yz1)).
move: (hrec n2 ltn2n Z2 (refl_equal (cardinal Z2)) C c2p).
move: (hrec n1 ltn1n Z1 (refl_equal (cardinal Z1)) C c1p).
clear c1p c2p hrec aux2 aux3 aux4.
move => [f1 [bf1 sf1 tf1] f1p][f2 [bf2 sf2 tf2] f2p].
pose f i := Yo (i = (csucc n1)) a
 (Yo (i <=c n1) (Vf f1 i) (Vf f2 (i -c (csucc n1)))).
have lt1:= (cltS n1N).
have p1: f (csucc n1) = a by rewrite /f; Ytac0.
have p2: forall i, i <=c n1 -> f i = Vf f1 i.
  move=> i lei. 
  by rewrite /f (Y_false (proj2(cle_ltT lei lt1))) (Y_true lei).
have p3 i: (csucc n1) <c i -> f i = Vf f2 (i -c (csucc n1)).
  move=> [lesi nsi]; rewrite /f; Ytac0; Ytac in1 => //.
  case:(cltNge lt1 (cleT lesi in1)). 
have p4 i: i <> \0c -> i <=c n1 -> inc (f i) Z1.
  move=> inz in1; rewrite (p2 _  in1);rewrite -tf1; Wtac; try fct_tac.
  by rewrite sf1; apply /(Nint1cP n1N).
have snN:= (NS_succ n1N).
have nn12: n  = ((csucc n1) +c n2) by rewrite  csumC csum_nS // csumC rel1.
have p5 i: csucc n1 <c i -> i <=c n ->
   inc  (i -c  (csucc n1)) (source f2).
  move=>  [n1i ni3] n2i; rewrite sf2 ; apply /(Nint1cP n2N).
  move:(NS_diff (csucc n1)(NS_le_nat n2i nN))  (cdiff_pr n1i).
  set d := _ -c _ ; move=> sN sv; split. 
    dneg dz; rewrite - sv dz; rewrite csum0r //; exact: (proj31 n1i).
  apply: (csum_le2l snN) => //; rewrite sv -nn12//.
have p6 i: (csucc n1) <c i -> i <=c n -> inc (f i) Z2.
  move=> in1 lin; rewrite (p3 _ in1) -tf2; Wtac; fct_tac.
set sf3 :=(Nint1c n).
have ta i: inc i sf3 -> inc (f i) E.
  move=> /(Nint1cP nN) [inz lein].
  have ci:= proj31 lein.
  have cn: cardinalp (csucc n1) by fprops.
  case: (cleT_el ci cn)=> aux1; last by apply: Z2E;apply: p6.
  case: (equal_or_not i (csucc n1)) => is1; first by rewrite is1 p1.
  have : i <c (csucc n1) by split.
  by move /(cltSleP n1N); move => lin1; apply: Z1E; apply: p4.
set F := Lf f sf3 E.
have sF: source F = sf3 by rewrite /F; aw.
have tF: target F = E by rewrite /F; aw.
have fF: function F by apply: lf_function.
have fpF: function_prop F sf3 E by [].
have injF: injection F.
  apply: lf_injective => // u v /(Nint1cP nN) [ua ub] /(Nint1cP nN) [va vb].
  wlog: u v ua ub va vb / u <c v.
     move => H; case: (cleT_ell (proj31 ub) (proj31 vb)) => //.
      by apply: H.
     by move => lvu /esym sf; symmetry; apply: H.
  move => luv.
  case: (equal_or_not u (csucc n1)) => un1.
    rewrite un1 p1; rewrite un1 in luv; move:(p6 v luv vb) => /Zo_S /setC1_P.
    by case=> _ => h h'; case: h.
    case: (cleT_el (proj31 ub) (proj32_1 lt1)).
      move => h1; move/ (cltSleP n1N): (conj h1 un1) => h2.
      move: (p4 _ ua h2)=> h3.
      case: (equal_or_not v (csucc n1)) => vn1.
        by rewrite vn1 p1=> h4; move/Zo_S: h3 => /setC1_P[_]; case.
      case: (cleT_el (proj31 vb) (proj32_1 lt1)).
        move => h1'; move/ (cltSleP n1N): (conj h1' vn1) => h2'.
        rewrite (p2 _ h2)(p2 _ h2'). 
        by apply: (proj2 (proj1 bf1)); rewrite  sf1; apply/(Nint1cP n1N).
      move => h4 h5; move: (p6 v h4 vb); rewrite Z2c => /setC_P [_]; case;ue.
    move => h1; move:(clt_ltT h1 luv)=> h2; rewrite  (p3 u h1) (p3 v h2)=> h3.
    move: (proj2 (proj1 bf2) _ _ (p5 u h1 ub) (p5 v h2 vb) h3) => h4.
    by rewrite - (cdiff_pr (proj1 h1)) - (cdiff_pr (proj1 h2)) h4.
exists F. 
  split => //.
  apply: bijective_if_same_finite_c_inj => //.
    by rewrite /F lf_source lf_target /sf3 nE card_Nint1c.
    by rewrite /F lf_source /sf3 /finite_set (card_Nint1c nN); apply /NatP.
move=> i i1 lin.
have inz: i <> \0c by move /cge1P: i1 => [_ /nesym].
move: (proj1 lin) => lein ;move: (NS_le_nat lein nN) =>  iN.
have i3: inc i sf3 by apply /(Nint1cP nN). 
have si3: inc (csucc i) sf3. 
  by apply /(Nint1cP nN); split; [ apply: succ_nz |  apply /cleSltP].
rewrite /F LfV // LfV //.
case: (cleT_el (proj31 lein) (CS_succ n1)) => aux1.
  case: (equal_or_not i (csucc n1)) => in1.
    have: inc (f (csucc i)) Z2.
       apply:p6; first by rewrite in1; apply: cltS. 
        by apply/(cleSltP (NS_lt_nat lin nN)).
    by move/Zo_hi; rewrite in1 p1.
  have lein1: i <=c n1 by apply /(cltSleP n1N); split.
  case: (equal_or_not i n1) => eqin1.
    by move:(p4 _ inz lein1); rewrite eqin1 p1;move/Zo_hi.
  have sin1: (csucc i) <=c n1  by apply /cleSltP.
  by rewrite p2 // p2 //; apply: f1p.
have p7:= (clt_leT aux1 (cleS iN)).
rewrite p3 // p3 //. 
have aux1':= (proj1 aux1).
move:(NS_diff (csucc n1) iN) (cdiff_pr  aux1').
set  k:= i -c  (csucc n1); move => kN kp.
have ->: (csucc i) -c  (csucc n1) = csucc k.
  rewrite - csucc_diff // cdiff_pr6//.
apply: f2p.
  apply: cge1; fprops.
  by move=> kz; case: (proj2 aux1); rewrite - kp kz (csum0r (CS_succ _)). 
by apply: (csum_lt2l snN) => //;rewrite kp -nn12.
Qed.

(* Surjectivity no needed in the proof above


have surjF: surjection F.
  apply: lf_surjective => // y yE.
  case: (equal_or_not y a).
    move=> ->; exists (csucc n1) => //; apply /(Nint1cP nN); split.
      apply: succ_nz.
    by apply /cleSltP.
  move=> ya; move: (cp _ _ yE aE ya) => [p7 _]; case: p7 => pc.
    have yz1: inc y Z1 by apply: Zo_i => //; apply /setC1_P;split => //.
    move: yz1; rewrite -tf1 => yt1. 
    move: bf1 => [_ srf1]; move: ((proj2 srf1) _ yt1) => [x xf1 ->].
    move: xf1; rewrite sf1; move /(Nint1cP n1N)=> [xnz xn1].
    exists x; last by rewrite p2.
     by apply /(Nint1cP nN);split => //; move: ltn1n => [/(cleT xn1) len1n _].
  have yz2: inc y Z2 by  apply: Zo_i => //; apply/ setC1_P.
  move: yz2; rewrite -tf2 => yt2. 
  move: bf2 => [_ srf2]; move: ((proj2 srf2) _ yt2) => [x xf2 ->].
  move: xf2; rewrite sf2; move /(Nint1cP n2N) => [xnz xn2].
  have xN:= (NS_le_nat xn2 n2N). 
  move: (cdiff_pr1 xN snN).
  set x1:= x +c (csucc n1) => x1n1.
  have x1p: (csucc n1) <c x1.
    have ->: (csucc n1) = \0c +c (csucc n1) by aw; fprops.
    rewrite /x1; apply: csum_Mlteq => //; fprops.
    by apply /strict_pos_P => //; apply:nesym.
  exists x1; last by rewrite (p3 _ x1p) x1n1.
  apply /(Nint1cP nN); split.
    move=> h; rewrite h in x1p; apply: (clt0 x1p).
    rewrite /x1 nn12 csumC;apply: csum_Mlele => //; fprops.
*)   


(** ---- Exercise 4.5. Let [E] be an ordered set, [k] the maximal number of
elements in a free subset. Then [E] can be partitioned into [k] totally ordered
subsets. 

Definitions: [Hw(k)] says that any free subset has at most [k] elements, 
[H(k)] says moreover that there is a free subset with [k] elements. 
[Cw(k)] says that there exists at most [k] totally ordered, mutually disjoint
sets  whose union is [E], [C(k)] says that this number is exactly [k], and 
the sets are non-empty. The claim is [H(k)] implies [C(k)]. We can restate it
as [Hw(k)] implies [Cw(k)]. Note that if we have a free subset with [k] 
elements, each element of the partition contains at most one element of the
free subset, so that if [Cw(k)] holds, there are [k] sets, none of them is empty.
 *)

(** Lemma: a finite non-empty set has a minimal element.

Assume [T] is a subset of a set partitioned by [Y], both sets have the same
finite number of elements; assume that the intersection of [T] and each [Yi] is
empty or a singleton. Then it is never empty. 
*)


Definition max_card_on_set X k :=
  (exists2 x, inc x X & cardinal x = k) /\
  (forall x, inc x X -> cardinal x <=c k).

Lemma max_card_on_set_unique X k1 k2:
  max_card_on_set X k1 -> max_card_on_set X k2 ->
  k1 = k2.
Proof.
move => [[x1 x1X x1v] h1] [[x2 x2X x2v] h2]. 
by move: (h1 x2 x2X)  (h2 x1 x1X); rewrite x1v x2v => l1 l2; apply: cleA.
Qed.


Lemma max_card_on_set_exists X n:
  natp n -> nonempty X ->
  (forall x, inc x X -> cardinal x <=c n) ->
  exists2 k, natp k & max_card_on_set X k.
Proof.
move=> nN neX hyp.
set T := fun_image X cardinal.  
have pa: (forall m, inc m T -> m <=c n) by move => m/funI_P [z /hyp zX ->].
have neT: nonempty T by  apply: funI_setne.
have TN: sub T Nat by move => m /pa /NS_le_nat; apply.
have fT: finite_set T.
   by apply: sub_finite_set (finite_Nintcc \0c n) => t /pa /(NintcP nN).
move: (finite_subset_Nat TN fT neT) => [m mT mg].
have mN: natp m by apply: TN.
move /funI_P:mT => [x mb mp].
have he: exists2 x, inc x X & cardinal x = m by ex_tac.
exists m => //;split => // t ts; apply: mg; apply/funI_P; ex_tac.
Qed.


Definition the_max_card_on_set X := select (max_card_on_set X) Nat.

Lemma the_max_card_on_set_prop X n (k := the_max_card_on_set X):
  natp n -> nonempty X ->
  (forall x, inc x X -> cardinal x <=c n) ->
  max_card_on_set X k /\ natp k.
Proof.
move => ha hb hc; apply: select_pr.
apply: (max_card_on_set_exists ha hb hc).
move => i j _ iv _ jv; apply:(max_card_on_set_unique iv jv).
Qed.


Lemma the_max_card_on_set_prop2 X n: natp n -> max_card_on_set X  n ->
   the_max_card_on_set X = n.
Proof.
move => ha hb.
have H: singl_val2 (inc^~ Nat) (max_card_on_set X).
  by move => a b /= _ ax _ bx; apply: (max_card_on_set_unique  ax bx). 
have exx:(exists2 x, inc x Nat & max_card_on_set X x) by exists n.
move: (select_pr  exx H); rewrite /the_max_card_on_set; set y := select _ _.
by move => [h1 _]; move: (max_card_on_set_unique h1 hb).
Qed.


Definition total_suborder r x := total_order (induced_order r x).
Definition total_suborders r := Zo (\Po (substrate r)) (total_suborder r).

Lemma free_subsetsP r x:
  inc x (free_subsets r) <-> (sub x (substrate r) /\ free_subset r x).
Proof.
split; first by move=> /Zo_P[/setP_P ha hb].
by move => [ha hb]; apply/Zo_P; split => //; apply /setP_P.
Qed.


Lemma total_subordersP r x:
  inc x (total_suborders r) <-> 
   (sub x (substrate r) /\ total_order (induced_order r x)).
Proof.
split; first by move=> /Zo_P[/setP_P ha hb].
by move => [ha hb]; apply/Zo_P; split => //; apply /setP_P.
Qed.


Lemma sub_total_suborders1 r F:
   order r -> sub F (substrate r) ->
   sub (total_suborders (induced_order r F)) (total_suborders r).
Proof.
move => or Fsr t /total_subordersP []; rewrite iorder_sr // => tF.
rewrite (iorder_trans _ tF) => tor.
by apply/total_subordersP; split => //; apply: (sub_trans tF Fsr).
Qed.

Lemma sub_total_suborders2 r X Y: order r ->
    inc X (total_suborders r) -> sub Y X -> inc Y (total_suborders r).
Proof.
move =>or /total_subordersP [ha hb] hc; apply/total_subordersP.
have s1 : sub Y (substrate (induced_order r X)) by rewrite iorder_sr//.
move: (sub_trans hc ha) => s2.
by move: (total_order_sub hb s1); rewrite (iorder_trans _ hc) => tor.
Qed.

Lemma total_suborder_prop r X: order r -> sub X (substrate r) ->
   {inc X &, forall x y, ocomparable r x y} ->
   inc X  (total_suborders r).
Proof.
move => or Xsr ac.
move: (iorder_osr or Xsr) => [or1 sr1].
apply/total_subordersP; split => //; split => //; rewrite sr1 => x y xA yA.
by case: (ac _ _ xA yA) => cp; [left |  right]; apply/iorder_gleP.
Qed.


Lemma sub_free_subsets r X Y:
    inc X (free_subsets r) -> sub Y X -> inc Y (free_subsets r).
Proof.
move => /free_subsetsP[Xs Fr] YX.
apply/free_subsetsP; split; first by apply: (sub_trans YX Xs).
by move => x y /YX xX /YX yX le; apply: Fr.
Qed.


Lemma empty_total_suborders r: inc emptyset (total_suborders r).
Proof.
apply/total_subordersP; split; [ fprops |].
have ->: (induced_order r emptyset) = emptyset.
  by apply/set0_P => t /setI2_P [_] /setX_P [_ /in_set0].
exact: (worder_total(proj1 set0_wor)).
Qed.

Lemma nonempty_total_suborders r: nonempty (total_suborders r).
Proof.
exists emptyset; apply: empty_total_suborders.
Qed.


Lemma nonempty_free_subsets r: nonempty (free_subsets r).
Proof.
by exists emptyset; apply/free_subsetsP; split ; [fprops|move => x y /in_set0].
Qed.


Definition order_width  r := max_card_on_set (free_subsets r).
Definition order_length  r := max_card_on_set (total_suborders r).
Definition the_order_width r := the_max_card_on_set (free_subsets r).
Definition the_order_length  r := the_max_card_on_set (total_suborders r).

Lemma order_width_exists r (k := the_order_width r):
  finite_set (substrate r) ->
  [/\ natp k, k <=c (cardinal (substrate r))  & order_width r k].
Proof.
move => /NatP nN.
have nef:= nonempty_free_subsets r.
have sf x: inc x (free_subsets r) -> cardinal x <=c (cardinal (substrate r)).
  by move => /Zo_S /setP_P/sub_smaller.
move: (the_max_card_on_set_prop nN nef sf)=>[ra rb]; split => //.
by move: (proj1 ra) => [x/sf ccx eq]; rewrite eq in ccx.
Qed.
  
Lemma order_length_exists r (k := the_order_length r):
  finite_set (substrate r) ->
  [/\ natp k, k <=c (cardinal (substrate r))  & order_length r k].
Proof.
move => /NatP nN.
have sf x:inc x (total_suborders r) -> cardinal x <=c cardinal (substrate r).
  by move => /Zo_S /setP_P/sub_smaller.
have nef:= nonempty_total_suborders r.
move: (the_max_card_on_set_prop nN nef sf) =>[ra rb]; split => //.
by move: (proj1 ra) => [x/sf ccx eq]; rewrite eq in ccx.
Qed.

Lemma cardinal_small_set x: small_set x -> cardinal x <=c \1c.
Proof.
case /small_set_pr.
  by move ->; rewrite cardinal_set0; fprops.
  move =>[v ->]; rewrite cardinal_set1; fprops.
Qed.

Lemma torder_set1 r x: order r -> inc x (substrate r) ->
  inc (singleton x) (total_suborders r).
Proof.
move => or xsr.
have h: sub (singleton x) (substrate r) by move => t /set1_P ->.
apply: (total_suborder_prop or h) => a b /set1_P-> /set1_P ->; left.
by order_tac.  
Qed.

Lemma set0_width: 
  the_order_width emptyset = \0c /\  the_order_length emptyset = \0c.
Proof.
have aux x: inc x (\Po substrate emptyset) -> cardinal x <=c \0c.
  rewrite (proj2 set0_osr); move/setP_P /sub_set0 ->.
  rewrite cardinal_set0;fprops.
split.
   apply:(the_max_card_on_set_prop2 NS0);split.
     exists emptyset; last exact: cardinal_set0.
     by apply/free_subsetsP; split ; [fprops|move => x y /in_set0].
   by move => x /Zo_S /aux.
apply:(the_max_card_on_set_prop2 NS0);split.
   exists emptyset; last exact: cardinal_set0.
   apply: empty_total_suborders.
by move => x /Zo_S/aux.
Qed.


Lemma set0_width_1 r: order r -> order_length r \0c -> substrate r = emptyset.
Proof.
move => or [_ ha]; case:(emptyset_dichot (substrate r)) => // - [x xsr].
case: (cleNgt(ha _ (torder_set1 or xsr))); rewrite cardinal_set1; exact: clt_01.
Qed.

Lemma set0_width_2 r: order r -> order_width r \0c -> substrate r = emptyset.
Proof.
move => or [_ ha]; case:(emptyset_dichot (substrate r)) => // - [x xsr].
case: (cleNgt(ha _  (Exercise1_5b or xsr))).
rewrite cardinal_set1; exact: clt_01.
Qed.

Lemma total_order_width r: total_order r ->
   nonempty (substrate r)  -> the_order_width r = \1c.
Proof.
move => tor [u usr].
apply:(the_max_card_on_set_prop2 NS1);split.
  exists (singleton u); first by apply:(Exercise1_5b (proj1 tor) usr).
  by rewrite cardinal_set1.
by move =>  x / (Exercise1_5e tor) /cardinal_small_set.
Qed.

Lemma total_order_width_contra r: order r -> 
  order_width r \1c -> total_order r.
Proof.
move => or [ha hb].
split => // u v usr vsr; ex_middle bad.
have hc: inc (doubleton u v) (free_subsets r).  
  apply/free_subsetsP; split; first by apply:sub_set2.
  move => a  b /set2_P; case => ->; case/ set2_P => -> // h; case: bad.
    by left.
  by right.
case: (equal_or_not u v) => neq.
  by case: bad; left; rewrite neq; order_tac.
move: (hb _ hc); rewrite (cardinal_set2 neq) => /cleNgt; case; exact: clt_12.
Qed.


Lemma diagonal_length E: nonempty E  ->
  the_order_length (diagonal E) = \1c.
Proof.
move => [u uE].
move: (diagonal_osr E) =>[or sr].
have usE: inc u (substrate (diagonal E)) by ue.
apply:(the_max_card_on_set_prop2 NS1); split.
  exists (singleton u); last by rewrite cardinal_set1.
  exact:(torder_set1 or usE).
move => x /total_subordersP [xE [ot ti]]; apply:cardinal_small_set.
move: (iorder_sr or xE) => si a b ax bx; move: (ti a b); rewrite si => h.
by case:(h ax bx) => /iorder_gle1 /diagonal_pi_P [].
Qed.


Lemma diagonal_length_contra r: order r ->
  order_length r \1c -> r = diagonal (substrate r).
Proof.
move => or [qa qb].
set_extens t; last by  move/diagonal_i_P => [{4} <- ps <-]; order_tac.
move => tr; apply /diagonal_i_P.
move: (proj41 or _ tr) (pr1_sr tr) (pr2_sr tr) => pt Ps Qs.
have qc:sub (doubleton (P t) (Q t)) (substrate r) by apply: sub_set2.
split => //; ex_middle bad.
have: inc (doubleton (P t) (Q t)) (total_suborders r).
  apply:(total_suborder_prop or qc) => a b.
  case/set2_P => ->;case/set2_P => ->.
  + by left; order_tac.
  + by left; rewrite /gle/related pt.
  + by right; rewrite /gle/related pt.
  + by left; order_tac.
move/qb; rewrite(cardinal_set2 bad)  => /cleNgt; case; exact: clt_12.
Qed.

Lemma diagonal_width r: order r -> finite_set (substrate r) ->
    (order_width r (cardinal (substrate r)) <-> r = diagonal (substrate r)).
Proof.
move => or fse.
split => hyp; last first.
  split. 
    exists (substrate r) => //; apply /free_subsetsP; split => //.
    by rewrite hyp => a b asr bsr /diagonal_pi_P [].
  by move => x /free_subsetsP [] /sub_smaller.
set_extens t; last by move/diagonal_i_P => [{4} <- ps <-]; order_tac.
move => tr; apply /diagonal_i_P.
move: (proj41 or _ tr) (pr1_sr tr) (pr2_sr tr) => pt Ps Qs.
split => //.
have cp: (gle r (P t) (Q t)) by move:tr; rewrite - {1} pt.
move: (proj1 hyp) => [X /free_subsetsP [Xsr Xfree] cX].
have XX := (cardinal_setC5 fse Xsr cX). 
rewrite - XX in Ps Qs.
exact: (Xfree (P t) (Q t) Ps Qs cp).
Qed.

Lemma total_order_length r: order r -> finite_set (substrate r) ->
    (order_length r (cardinal (substrate r)) <-> total_order r).
Proof.
move => or fse.
split => hyp; last first.
  split. 
    exists (substrate r) => //; apply /total_subordersP; split => //.
     by apply:total_order_sub.
  by move => x /total_subordersP [] /sub_smaller.
move: (proj1 hyp) => [X /total_subordersP [Xsr Xt] cX].
by move: Xt; rewrite (cardinal_setC5 fse Xsr cX) iorder_substrate.
Qed.

Lemma Dilworth_dual r (k := the_order_length r): order r ->
  (exists2 n, natp n & 
     forall x, inc x (total_suborders r) -> cardinal x <=c n) ->
  exists A,
  [/\ natp k, order_length r k
    & [/\ partition_s A (substrate r),
    cardinal A = k & sub A (free_subsets r)]].
Proof.   
move => or ha.
have [res1 kN]: order_length r k /\ natp k.
  move: ha =>[n nN np].
  apply: (the_max_card_on_set_prop nN (nonempty_total_suborders r) np).
clear ha. 
move: (res1) => [[C Cto ca] cb]. 
set Cs := (total_suborders r).
pose p x X:= [/\ inc X Cs, inc x X & forall y, inc y X -> gle r y x].
pose P x := Zo Cs (p x).
pose f x := the_max_card_on_set (P x).
have Ha x: inc x (substrate r) -> inc (singleton x) (P x).
  move => xsr.
  move: (set1_1 x) => xx.
  move: (torder_set1 or xsr) => hb.
  by apply: (Zo_i  hb); split => // y /set1_P ->; order_tac.
have bdP x X: inc X (P x) -> cardinal X <=c k.
  by move => /Zo_S; apply:cb.
have Hx x: inc x (substrate r) -> max_card_on_set (P x) (f x) /\ natp (f x).
  move => xsr.
  have neP: nonempty (P x) by exists (singleton x); apply: Ha.
  apply: (the_max_card_on_set_prop kN neP (bdP x)).
have fbd x: inc x (substrate r) -> \1c <=c (f x) /\ f x <=c k.
  move => xsr; move: (Hx x xsr) => [[qa qb] qc]; split.
    by move: (qb _ (Ha x xsr)); rewrite cardinal_set1.
  by move: qa => [X] /Zo_S /cb le <-.
case: (emptyset_dichot (substrate r)) => Enz. 
  exists emptyset; split => //.
  move:Cto =>/Zo_P [/setP_P /sub_smaller]; rewrite Enz cardinal_set0 ca.
  move => /cle0 -> _; split => //;last by move => t/in_set0.
  by split;[hnf; rewrite setU_0; split => // u v /in_set0| move => t /in_set0].
case: (equal_or_not k \0c) => knz.
  case: Enz => x /fbd [ua ub]; move: (cleT ua ub) => /cleNgt; case; ue. 
have finc x y: glt r x y -> f x <c f y.
  move => [lxy nxy]; move: (arg1_sr lxy) (arg2_sr lxy) => xsr ysr.
  move: (Hx _ xsr) => [[[c /Zo_P[/Zo_P[/setP_P ra rb] [_ qb qc]] lc] _] fN].
  set Y := c +s1 y.
  have Ysr: sub Y (substrate r) by move => t/setU1_P; case => h; fprops; ue.
  have bmax: forall t, inc t Y -> gle r t y.
    move => t /setU1_P; case => h ; first by move: (qc _ h) => rc; order_tac.
    by rewrite h; order_tac.
  have yY: inc y Y by apply: setU1_1.
  have tor: total_order (induced_order r Y).
    move: (iorder_osr or Ysr) => [oa ob]; split => //.
    rewrite ob => a b aY bY; case/setU1_P: (bY); last first.
      by move => ->; left; apply/(iorder_gle0P r aY yY); apply: bmax.
    move => bX;  case/setU1_P: (aY); last first.
      by move ->; right; apply/(iorder_gle0P r bY yY); apply: bmax.
    move => aX; move: (proj2 rb a b); rewrite (iorder_sr or ra) => h.
    by case: (h aX bX) => /iorder_gle1 cp; [left | right]; apply/(iorder_gleP). 
  have Ys: inc Y Cs by apply: Zo_i => //; apply/setP_P.
  have Yb: inc Y (P y) by apply:(Zo_i Ys); split => //.
  have bx:  ~ inc y c by  move => /qc h; case:  nxy; order_tac.
  move: (proj2(proj1 (Hx _ ysr)) _  Yb).  rewrite /Y (csucc_pr bx); rewrite lc.
  by move/(cleSltP fN).
pose A i := Zo (substrate r) (fun z => f z = i).
pose AA := fun_image (Nint1c k) A.
have ra : partition_w AA (substrate r).
  split. 
   set_extens t.
     by move/setU_P=> [u tu /funI_P [i _ uv]]; move: tu; rewrite uv => /Zo_S.
   move => tsr; move /(Nint1cPb kN): (fbd _ tsr)=> fi. apply/setU_P.
   by exists (A (f t)); [apply/Zo_P | apply:funI_i].
  move => a b /funI_P[i ia ->] /funI_P[j ka ->]; mdi_tac bad => t.
  by move=> /Zo_P [_ fti] /Zo_P[_ ftj]; case: bad; rewrite - fti - ftj.
have Hb x: inc x AA -> inc x (free_subsets r).
  move/funI_P => [i _ ->]; apply: Zo_i; first by apply/setP_P => t /Zo_S.
  move => a b /Zo_P [_ fa] /Zo_P[_ fb] leab.
  by ex_middle bad; case: (proj2(finc _ _  (conj leab bad))); rewrite fa fb.
have Akne: nonempty (A k).
  suff:  exists2 x, inc x (substrate r) & f x = k. 
    by move=> [x xde fx]; exists x; apply: Zo_i.
  move: (Cto) =>/Zo_P [/setP_P qa qb].
  have fsC: finite_set C by apply /NatP; ue.
  have neC:nonempty C by  apply/cle1P; rewrite ca; apply: cge1; fprops.
  have sr:  substrate (induced_order r C) = C by rewrite iorder_sr.
  move: (finite_set_torder_greatest qb); rewrite sr => h.
  move: (h fsC neC) => [x []]; rewrite sr => xc xm.
  have cp: inc C (P x). apply:(Zo_i Cto); split => // y yC.
    exact: (iorder_gle1 (xm y yC)).
  move: (qa x xc) => xsr; exists x => //; apply: cleA. 
      exact: (proj2 (fbd _ xsr)).
  by move: (Hx x xsr) => [ [_] xp] _; move: (xp _ cp); rewrite ca.
have neA i: inc i (Nint1c k) -> nonempty (A i).
  case/(Nint1cPb kN);move: i; apply:(Nat_induction4 NS1 kN Akne).
  move => i le1 le2 [u /Zo_P [usr fu]].
  move: (Hx u usr)=> [[[c /Zo_hi [qa qb qc] cs] _] nv].
  move:(NS_lt_nat le2 kN) => iN. 
  set D := c -s1 u.
  have cD: cardinal D = i by rewrite /D - (cpred_pr5 qb) cs fu (cpred_pr2 iN).
  have neD: nonempty D by  apply/cle1P; ue.
  have fsD: finite_set D by apply /NatP; ue.
  have Dc: sub D c by move => t /setC1_P [].
  have qf: inc D Cs by apply: (sub_total_suborders2 or qa Dc).
  move/total_subordersP: (qf)=> [Dsr qe].
  move: (iorder_sr or Dsr)=> ssr.
  move: (finite_set_torder_greatest qe); rewrite ssr => h.
  move: (h fsD neD)=> [x []]; rewrite ssr => xD xms.
  have xms' y : inc y D -> gle r y x by move/xms => /iorder_gle1.
  move/setC1_P: (xD)=>[xc xny].
  have qg: inc D (P x) by apply: (Zo_i qf).
  exists x. apply: (Zo_i (Dsr _ xD)); apply: cleA.
    by apply/(cltSleP iN);rewrite - fu; apply:finc; split=> //;apply: (qc _ xc).
  by  move:(proj2 (proj1 (Hx x (Dsr _ xD))) _ qg); rewrite cD.
exists AA; split => //;split => //.
  by split => // t /funI_P [i ii ->]; apply: neA.
rewrite - (card_Nint1c kN).
apply:cardinal_fun_image=> a b ai bi  eqa.
move: (neA _ ai) => [x xA]; move/Zo_P: (xA) => [_ <-].
by rewrite eqa in xA;  move/Zo_P: (xA) => [_ <-].
Qed.

Lemma Dilworth_lemma_v1 r : order r -> finite_set (substrate r) ->
  cardinal (substrate r) <=c (the_order_length r) *c (the_order_width r).
Proof.
move => or fsr.
move: (order_length_exists fsr) (order_width_exists fsr).
set k := the_order_width r; set l := the_order_length r.
move => [lN lb [qa qb]] [kN kb [qc qd]].
have hll: (exists2 n, natp n &
   forall x, inc x (total_suborders r) -> cardinal x <=c n) by exists l.
move:(Dilworth_dual or hll); rewrite -/l.
move => [A [_ _ [pa pb pc]]].
rewrite - (proj1 (proj1 pa)) - pb cprodC.
by apply: cardinal_uniona => x /pc /qd.
Qed.
  
  
Lemma Dilworth_lemma_v2 r n m:
  order r -> natp n -> natp m -> cardinal (substrate r) = csucc (n *c m) ->
  (exists2 B, inc B (free_subsets r) & cardinal B = csucc m) \/
  exists2 A, inc A (total_suborders r) & cardinal A = csucc n.
Proof.
move => or nN mN csr.
move: (NS_succ (NS_prod nN mN)); set p := csucc _ => pN.
have fsr: finite_set (substrate r) by apply/NatP; ue.
move:(Dilworth_lemma_v1 or fsr).
move: (order_length_exists fsr) (order_width_exists fsr).
set a := (the_order_length r); set b := (the_order_width r); rewrite csr.
move => [aN ab [ [A Af cA] _]] [bN bb [ [F Ff cF] _]] le1.
case: (NleT_el aN nN) => le2.
  case: (NleT_el bN mN) => le3.
    case: (cleNgt(cleT le1 (cprod_Mlele le2 le3))); apply: cltS; fprops.
  left; move/(cleSltP mN): le3; rewrite -(card_card (CS_succ m)) - cF.
  move/ (sub_smaller_contra) => [Y yf ->]; exists Y => //.
  move/free_subsetsP:Ff => [ra rb].
  apply/free_subsetsP; split; first by apply: (sub_trans yf ra).
  by move => u v /yf ua /yf ub; apply: rb.
right; move/(cleSltP nN): le2; rewrite -(card_card (CS_succ n)) - cA.
move/ (sub_smaller_contra) => [Y yf ->]; exists Y => //.
exact:(sub_total_suborders2 or Af yf). 
Qed.


Lemma Erdos_Szerkeres r n m f (D := csucc (n *c m)) :
  total_order r -> natp n -> natp m -> fgraph f ->
  domain f = D -> sub (range  f) (substrate r) ->
  {inc D &, injective (Vg f)} ->
  (exists B, [/\ sub B D, cardinal B = csucc m &
     forall i j, inc i B -> inc j B -> i <c j -> glt r (Vg f j) (Vg f i)])
  \/ exists A, [/\ sub A D,  cardinal A = csucc n &
    forall i j, inc i A -> inc j A -> i <c j -> glt r (Vg f i) (Vg f j)].
Proof.
move => [or tor] nN mN fgf df rgf injf.
move: (NS_succ (NS_prod nN mN)); rewrite -/D => DN.
pose comp i j := i <=c j /\ gle r (Vg f i) (Vg f j). 
pose cp := graph_on comp D.
have: order_r  comp.
  split.
    by move => i j k [ha hb] [hc hd]; split; [ apply: (cleT ha hc)| order_tac].
  by move => i j [ha hb][hc hd]; apply: cleA.
  move => i j [[ha hb _] hc]; move: (arg1_sr hc)  (arg2_sr hc) => ue ve.
  by split; split; try order_tac => //; apply: cleR.
move/(order_from_rel D); rewrite -/cp => or1.
have sr1: substrate cp = D.
    apply:graph_on_sr=> a aD;split.
      by apply: cleR;move/(NltP DN):aD => /proj31_1.
    order_tac;apply: rgf;apply: inc_V_range => //; ue.
have csr1: cardinal (substrate cp) = csucc (n *c m) by  rewrite sr1 card_nat.
case: (Dilworth_lemma_v2 or1 nN mN csr1).
   move => [B /Zo_P [/setP_P sb pb] cb]; left; exists B; split => //; first ue.
   move => i j iB jB [cij nij]; split; last first.   
     rewrite sr1 in sb;move => bad; case:nij.
     by rewrite (injf j i (sb _ jB) (sb _ iB) bad).
  rewrite sr1 in sb.
  have jsr: inc (Vg f j) (substrate r).
    by apply: rgf; apply: inc_V_range => //; rewrite df; apply: sb.
  have isr: inc (Vg f i) (substrate r).
    by apply: rgf; apply: inc_V_range => //; rewrite df; apply: sb.
  case: (tor  (Vg f j) (Vg f i) jsr isr) => // ler.
  have h: gle cp i j by apply/graph_on_P1; split => //; apply: sb.
  case: nij; exact: (pb i j iB jB h).
move => [A /total_subordersP [Asr tor1] xA]; right;exists A.
have AD: sub A D by move: Asr; ue. 
split => // i j iA jA [lik nij]; split.
  move: (proj2 tor1 i j); rewrite iorder_sr // => h.
  move: (h iA jA); case; move/iorder_gle1 /graph_on_P1.
    by move => [_ _ [pa pb]] //.
  by move => [_ _ [pa pb]]; case: nij; apply: cleA.
move => bad; case:nij.
exact:(injf i j (AD _ iA) (AD _ jA) bad).
Qed. 

Lemma Sperner_1 A B k: natp k -> cardinal A = k -> cardinal B = k ->
  sub A B -> A = B.
Proof.
move => kN cA cB sAB.
apply: (extensionality sAB); apply:empty_setC.
move: (cardinal_setC2 sAB); rewrite - csum2cl - csum2cr cA cB -{1}(Nsum0r kN).
have nD: natp (cardinal (B -s A)).
  have s1: sub (B -s A) B by move => t /setC_P [].
  have fsj: finite_set B by apply/NatP; ue.
  apply /NatP; apply: (sub_finite_set s1 fsj).
by move/ (csum_eq2l kN NS0 nD); move /esym /card_nonempty.
Qed.

Lemma Sperner_2 E k (F := subsets_with_p_elements k E): natp k ->
  free_subset (subp_order E) F. 
Proof.
move => kN i j /Zo_P [/setP_P iE ci] /Zo_P[ /setP_P jE cj].
move/ sub_gleP => [_ _ sij]; apply: (Sperner_1 kN ci cj sij).
Qed.

Lemma Sperner_b1 n k: natp n -> k <=c n ->
   (factorial n) <=c 
   (binom n (chalf n)) *c ((factorial k) *c (factorial (n -c k))).
Proof.
move => nN lkn.
move:(NS_le_nat lkn nN) => kN. 
rewrite - (binom_good nN kN lkn).
by apply: cprod_Mleeq; apply: binom_max.
Qed.

Definition is_half_n n k := (k = (chalf n) \/ n -c k = (chalf n)).
  
Lemma Sperner_b2 n k: natp n -> k <=c n ->
   (factorial n) =
     (binom n (chalf n)) *c ((factorial k) *c (factorial (n -c k))) ->
   is_half_n n k.
Proof.
move => nN lkn.
move:(NS_le_nat lkn nN)(NS_diff k nN) => kN dN h. 
apply/(binom_monotone_max_arg nN lkn).
move: h; rewrite - (binom_good nN kN lkn) ; apply: cprod_eq2r.
- by apply:NS_prod; apply: NS_factorial.
- by apply: NS_binom.
- by apply: (NS_binom nN (NS_half nN)).
- by apply: cprod2_nz; apply: factorial_nz.
Qed.

Section Sperner.
Variable E: Set.
Hypothesis fsE: finite_set E.
Let r := subp_order E.
Let n := cardinal E.
Let cn := binom n (chalf n).

Lemma  Sperner_p0: natp n.
Proof. by apply/NatP. Qed.
  
Lemma Sperner_p1 k: k <=c n ->
  free_subset r (subsets_with_p_elements k E).
Proof.
move => h; move: (NS_le_nat h Sperner_p0) => kN.
by apply:(Sperner_2).
Qed.

Lemma Sperner_p2 k: k <=c n ->
  cardinal (subsets_with_p_elements k E) = binom n k.
Proof.
move: Sperner_p0 => nN h; move: (NS_le_nat h nN) => kN.
by rewrite - (card_p_subsets nN kN (erefl n)).
Qed.

Lemma Sperner_p3 k: k <=c n -> binom n k <=c cn.
Proof. by move: Sperner_p0 => nN h; apply: binom_max. Qed.

Lemma Sperner_p4 A:
  inc A (free_subsets  r) <-> sub A (\Po E) /\ free_subset r A.
Proof.
move: (subp_osr E) => [or sr]; rewrite/free_subsets sr.
by split;[ move/Zo_P => [/setP_P] | move => [/setP_P ha hb0]; apply: Zo_i].
Qed.

Lemma Sperner_p5 k: k <=c n ->
  inc (subsets_with_p_elements k E) (free_subsets r).
Proof.
by move =>h; apply/Sperner_p4; split;[ apply: Zo_S | apply:Sperner_p1].
Qed.
  
Lemma Sperner_3 C: inc C (total_suborders r) -> {inc C &, injective cardinal}.
Proof.
move => /total_subordersP [qa qb] A B AC BC /= sc.
move:(subp_osr E) Sperner_p0 => [or sr] nN.
have kN: natp (cardinal A).
  by apply /(NS_le_nat _ nN) /sub_smaller /setP_P; rewrite - sr;apply: qa.
move: (proj2 qb A B); rewrite iorder_sr// => h; case: (h AC BC) => /iorder_gle1 /sub_gleP.
by move/proj33 => sAB; apply:(Sperner_1 kN _ _ sAB).
by move/proj33 => sAB; symmetry;apply:(Sperner_1 kN _ _ sAB).
Qed.

Lemma Sperner_4 C: inc C (total_suborders r) -> cardinal C <=c (csucc n).
Proof.
move =>h; move: (Sperner_3 h) => ci. move:h=> /total_subordersP [qa qb].
move:(subp_osr E) Sperner_p0 => [or sr] nN.
have aux A: inc A C -> cardinal A <=c n.
  by rewrite sr in qa;  move/qa  => /setP_P /sub_smaller.
rewrite - (cardinal_fun_image ci) - (card_Nintc nN).
by apply: sub_smaller => t /funI_P [A /aux c ->]; apply/(NintcP nN).
Qed.

Definition Sperner_mx_chain :=
  (Zo (total_suborders r) (fun C =>  cardinal C = csucc n)).

Definition chain_of_fun  g := fun_image (csucc n) (Vfs g).

Lemma Sperner_5 g: bijection_prop g n E  ->
  inc (chain_of_fun g) Sperner_mx_chain. 
Proof.
move => [ [[fg ing] sjg] sg tg].
move:(subp_osr  E) Sperner_p0 => [or sr] nN.
have H i: i <=c n -> sub i (source g) by  move/proj33; rewrite sg.
have pa : {inc (csucc n) &, injective (Vfs g)}. 
  move => i j /(NleP nN) lin  /(NleP nN) ljn ss.
  move: (NS_le_nat lin nN)(NS_le_nat ljn nN) => iN jN.
  move: (H _ lin) (H _ ljn) => isg jsg.
  case: (NleT_ell iN jN) => // lt1.
    have ij: inc i j by apply/NltP.
    have: inc (Vf g i) (Vfs g j) by apply/(Vf_image_P fg jsg); ex_tac.
    rewrite - ss => /(Vf_image_P fg isg) [k ki kv].
    move: (ing i k (jsg _ ij) (isg _ ki) kv) => eik.
    by move/(NltP iN): ki =>/proj2; rewrite eik; case.
  have ij: inc j i by apply/NltP.
  have: inc (Vf g j) (Vfs g i) by apply/(Vf_image_P fg isg); ex_tac.
  rewrite ss => /(Vf_image_P fg jsg) [k ki kv].
  move: (ing j k (isg _ ij) (jsg _ ki) kv) => eik.
  by move/(NltP jN): ki =>/proj2; rewrite eik; case.
have aux k: k <=c n -> sub (Vfs g k) E.
  move => skn; move:  (H _ skn) => s1.
  move => t /(Vf_image_P fg s1) [u uk ->]; Wtac.
have sC: sub (chain_of_fun g) (substrate (subp_order E)).
  by rewrite sr=> t /funI_P [i /(NleP nN) lin ->]; apply/setP_P; apply: aux.
apply: Zo_i; last by rewrite(cardinal_fun_image pa) card_card; fprops.
apply:(total_suborder_prop or sC).
move => x y /funI_P [i /(NleP nN) lin ->]  /funI_P [j /(NleP nN) ljn ->].
move: (aux _ lin) (aux _ ljn)=> iA iB.
move: (H _ lin) (H _ ljn) => isg jsg.
case: (cleT_ee (proj31 lin) (proj31 ljn)) => cij; [left | right].
  apply/subp_gleP; split => // t /(Vf_image_P fg isg)  [u ui ->].
  by apply/(Vf_image_P fg jsg); exists u => //; apply: (proj33 cij).
apply/subp_gleP; split => // t /(Vf_image_P fg jsg)  [u ui ->].
by apply/(Vf_image_P fg isg); exists u => //; apply: (proj33 cij).
Qed.  

Lemma Sperner_6: order_length r (csucc n).
Proof.
split; last by apply:Sperner_4.
have: n \Eq E by apply/card_eqP; rewrite /n double_cardinal.
move/ (equipotent_ex_pr) /Sperner_5 /Zo_P=> [fa fb]; ex_tac.
Qed.

Lemma Sperner_7 C: inc C Sperner_mx_chain ->
   lf_axiom  cardinal C (csucc n) /\ bijection (Lf cardinal C (csucc n)).
Proof.
move =>  /Zo_P[ha hb].
move: (Sperner_3 ha) => hc.
move:(subp_osr E) Sperner_p0 => [or sr] nN.
move:ha=> /total_subordersP [qa qb].
have aux A: inc A C -> cardinal A <=c n.
  by rewrite sr in qa;  move/qa  => /setP_P /sub_smaller.
have ax: lf_axiom  cardinal C (csucc n) by move => t /aux /(NleP nN).
split => //;apply: bijective_if_same_finite_c_inj; aw.
- by rewrite hb (card_nat (NS_succ nN)).
- apply /NatP; rewrite hb; fprops.
- by apply: lf_injective.
Qed.
  
  
Lemma Sperner_8 C (F := Vf (inverse_fun (Lf cardinal C (csucc n)))):
   inc C Sperner_mx_chain ->
   forall i, i <=c n -> inc (F i) C /\ cardinal (F i) = i.
Proof.
move:Sperner_p0  => nN /Sperner_7 [ax card_b] i lin.
have itg: inc i (target (Lf cardinal C (csucc n))) by aw; apply/(NleP nN).
move: (inverse_Vis card_b itg);aw =>  ifC; split => //.
move: (inverse_V card_b itg); rewrite LfV//.
Qed.

Lemma Sperner_9 C (F := Vf (inverse_fun (Lf cardinal C (csucc n))))
         (xi := fun i =>  union (F (csucc i) -s (F i))):
   inc C Sperner_mx_chain ->
   forall i, i<c n -> F (csucc i) = (F i) +s1  (xi i).
Proof.
move => Cm.
move: (Sperner_8 Cm) => Ha.
move:Cm => /Zo_P[ha hb].
move:ha=> /total_subordersP [qa qb].
move:(subp_osr E) Sperner_p0 => [or sr] nN.
have Xig i j:  i <=c n -> j <=c n -> i <=c j -> sub (F i) (F j).
  move => lin ljn lij.
  move: (Ha _ lin)  (Ha _ ljn)=> [ra rb] [rc rd].
  move: (proj2 qb (F i) (F j)); rewrite iorder_sr // => h.  
  case:(h ra rc) => /iorder_gle1/sub_gleP/proj33 //.
  by move/sub_smaller; rewrite rb rd => ji; rewrite (cleA ji lij).
have rec A B: sub A B /\ singletonp (B -s A) -> B = A +s1 (union (B -s A) ).
  by move => [sab [t tv]]; rewrite - {1} (setU2_Cr sab) tv setU_1.
move => i lin; apply: rec.
move: (NS_lt_nat lin nN) => iN.
move/(cleSltP iN): (lin) => sin.
move: (Xig i (csucc i) (proj1 lin) sin (cleS iN)) => sii.
split => //; apply /set_of_card_oneP.
move:(Ha _ (proj1 lin)) (Ha _ sin) => [_ rc] [_ rd].
have fsX:finite_set (F (csucc i)) by apply/NatP; rewrite rd; fprops.
by rewrite(cardinal_setC4 sii fsX) rc rd  (Nsucc_rw iN) csumC(cdiff_pr1 NS1).
Qed.

Lemma Sperner_10 C (F := Vf (inverse_fun (Lf cardinal C (csucc n))))
         (g := Lf (fun i =>  union (F (csucc i) -s (F i))) n E):
   inc C Sperner_mx_chain ->
   bijection_prop g n E /\ C = chain_of_fun g.
Proof.
move => Cm.
move:(subp_osr E) Sperner_p0 => [or sr] nN.
move: (Sperner_8 Cm) (Sperner_9 Cm); rewrite -/F => Ha Hb.
move: (Sperner_7 Cm) =>[ax card_b].
move:Cm => /Zo_P[ha hb].
move:ha=> /total_subordersP [qa qb].
pose xi i := union (F (csucc i) -s F i).
have Xie i: i <c n -> inc (xi i) (F (csucc i)) by move/Hb ->; fprops.
have axg: lf_axiom xi n E.
  move => i /(NltP nN) lin; move: (Xie _ lin) (NS_lt_nat lin nN)=> in1 iN.
  by move/(cleSltP iN): lin => /Ha/proj1 /qa; rewrite sr; move/setP_P; apply.
have Xif i j: i <c j -> j <=c n -> inc (xi i) (F j).
  move => lij ljn.
  move:(NS_le_nat ljn nN) => jN.
  move:(NS_lt_nat lij jN) => iN.
  move: (Xie _ (clt_leT lij ljn)) => h.
  move/(cleSltP iN): lij => lij.
  move: (Ha _ (cleT lij ljn)) (Ha _ ljn) => [ra rb] [rc rd].
  move: (proj2 qb (F (csucc i)) (F j)); rewrite iorder_sr // => hyp.  
  case:(hyp ra rc) => /iorder_gle1/sub_gleP/proj33; first by apply.
  by move/sub_smaller; rewrite rb rd => ji; rewrite (cleA ji lij).
have Xih i: i <c n -> ~inc (xi i) (F i). 
   move => lin xx; move: (f_equal cardinal (Hb i lin)); rewrite (setU1_eq xx).
   move: (NS_lt_nat lin nN) => iN.
   rewrite (proj2(Ha i (proj1 lin))).
   move/(cleSltP iN): lin => /Ha/proj2 ->.
   exact: (nesym (proj2 (cltS iN))).
have bgp: bijection_prop g n E.
  rewrite /g;saw;apply: bijective_if_same_finite_c_inj; aw.
  - by rewrite /n double_cardinal.
  - by apply: finite_set_nat.
  - apply: lf_injective => // i j /(NltP nN) lin /(NltP nN) ljn => sxi.
    move: (NS_lt_nat lin nN) (NS_lt_nat ljn nN) => iN jN.
    case: (NleT_ell iN jN) => // lij.
      by case: (Xih j ljn); move: (Xif i j lij (proj1 ljn)); rewrite /xi sxi.
    by case: (Xih i lin); move: (Xif j i  lij (proj1 lin)); rewrite /xi - sxi.
move: (bgp) => [[injg [fg sjg]] sg tg].
have Xik i: i <=c n -> Vfs g i = F i.
  move => lin; move:(NS_le_nat lin nN) => iN.
  have sig: sub i (source g) by rewrite sg; exact: (proj33 lin).
  move: (proj2 (Ha _ lin)) => c1.
  have fs1: (finite_set (F i)) by apply /NatP; rewrite c1.
  have sa: sub (Vfs g i) (F i).
    move => t /(Vf_image_P fg sig)  [u /(NltP iN) ui ->]; rewrite/g LfV//.
      by apply: Xif.
    by apply/(NltP nN); apply: (clt_leT ui lin).
  apply: (cardinal_setC5 fs1 sa). 
  by rewrite c1 (cardinal_image sig injg) card_nat.
split => //;set_extens t.
  move => tC.
  have tc: inc t (source (Lf cardinal C (csucc  n))) by aw.
  move: (Vf_target (proj1(proj1 card_b)) tc); aw => lin.
  move/(NleP nN): (lin) => liin.
  by apply/funI_P; ex_tac;rewrite (Xik _ liin) - {1} (inverse_V2 card_b tc); aw.
move=>/funI_P [i /(NleP nN) lin ->]; rewrite (Xik _ lin).
exact: (proj1 (Ha _ lin)).
Qed.


Lemma Sperner_11 w i (C :=  chain_of_fun w) 
     (F := Vf (inverse_fun (Lf cardinal C (csucc n)))):
  bijection_prop w n E -> i <=c n -> Vfs w i = F i.
Proof.
move => wp lin.
move: (Sperner_5 wp) Sperner_p0 => CC nN.
have ci: cardinal i = i by apply: (card_card (proj31 lin)).
move: (Sperner_7 CC) => [Ha Hb].
move: (wp) => [[iw _] sw tw].
have  siw: sub i (source w) by rewrite sw; apply: (proj33 lin).
have qa: inc (Vfs w i) C by  apply/funI_P; exists i => //; apply /NleP.
have qb:  cardinal (Vfs w i) = i by rewrite (cardinal_image siw iw).
by rewrite - (inverse_V2 Hb (y := Vfs w i)) //  -/F; aw;bw => //; ue.
Qed.

Lemma Sperner_12 w i: bijection_prop w n E -> i <c n ->
   (Vf w i) = union (Vfs w (csucc i) -s Vfs w i).
Proof.
move => [[iw [fw _]] sw tw] lin.
move:Sperner_p0  => nN.
move: (NS_lt_nat lin nN) => iN.
set A := Vfs w (csucc i); set B := Vfs w i. 
suff: A -s B = singleton (Vf w i) by move ->; rewrite setU_1.
have lsin: csucc i <=c n by apply/(cleSltP iN).
have sisw: sub (csucc i) (source w) by rewrite sw; exact: (proj33 lsin).
have isw: sub i (source w) by rewrite sw; exact: (proj33 (proj1 lin)).
apply: set1_pr.
  apply/setC_P; split.
    by apply/(Vf_image_P fw sisw); exists i => //; apply: Nsucc_i.
  have iisw: inc i (source w) by rewrite sw; apply/NltP.
  move/(Vf_image_P fw isw) => [j uj sva].
  move: (proj2 iw i j iisw (isw _ uj) sva) => ij.
  by move: (ordinal_decent OS_omega iN); rewrite {1} ij; case.
move => t  /setC_P [/(Vf_image_P fw sisw) [j jsi ->] h].
move/(NleP iN): jsi; case/ cle_eqVlt; [by move -> | move => lij; case: h].
by apply /(Vf_image_P fw isw); exists j => //; apply/NltP.
Qed.

Lemma Sperner_13 w1 w2: bijection_prop w1 n E -> bijection_prop w2 n E ->
   chain_of_fun w1=  chain_of_fun w2 -> w1 = w2.
Proof.
move => p1 p2 sv.
move:Sperner_p0  => nN.
move:(p1)(p2) => [qa qb qc][qd qe qf].
apply: function_exten; try fct_tac; try ue; rewrite qb => i iin.
move/(NltP nN): (iin) => lin. 
have lein: csucc i <=c n by apply/(cleSlt0P (proj31_1 lin) nN).
rewrite (Sperner_12 p1 lin) (Sperner_12 p2 lin).
rewrite (Sperner_11 p1 lein)  (Sperner_11 p2 lein) (Sperner_11 p2 (proj1 lin)).
by rewrite (Sperner_11 p1 (proj1 lin)) sv.
Qed.

Lemma Sperner_14: cardinal Sperner_mx_chain = factorial n.
Proof.
have: n \Eq E by apply/card_eqP; rewrite /n double_cardinal.
move/ (equipotent_ex_pr); set f := (equipotent_ex n E) => fp.
move:Sperner_p0  => nN.
pose phi g:=  chain_of_fun (f \co g).
suff: bijection (Lf  phi (permutations n) Sperner_mx_chain).
  have fse: finite_set n by apply: finite_set_nat.
  move/card_bijection; aw => <-.
  by  rewrite card_permutations // /n double_cardinal.
have ax: lf_axiom phi (permutations n) Sperner_mx_chain.
  by move => t /permutationsP bpt; move: (compose_bp bpt fp) => /Sperner_5.
move: (inverse_bij_bp fp)=> fip.
apply: (lf_bijective ax); last first.
  move => C hc; move: (Sperner_10 hc)=> []; set g := Lf _ _ _ => gp ->.
  move: (compose_bp gp fip) => cb.
  exists ((inverse_fun f) \co g); first by apply/permutationsP.   
  move: fp gp => [Ha _ Hb] [[[Hc _] _] _ Hd ].
  rewrite /phi compf_lK' //; ue.
move => u v /permutationsP up /permutationsP vp.
move: (compose_bp up fp) (compose_bp vp fp); rewrite /phi => b1 b2 sv.
have: (f \co u) = (f \co v) by apply:Sperner_13.
move: fp up vp =>[bf sf _] [[[fu _] _] _ tu] [[[fv _] _] _ tv].
move: (proj1 (proj1 bf))=> ff;  apply:(compf_regr bf); split => //; ue.
Qed.

Lemma Sperner_15 U V (a:= cardinal U) (b := cardinal V):
  natp a -> natp b -> disjoint U V ->
    exists2 g, bijection_prop g (a+c b) (U \cup V)  & Vfs g a = U.
Proof.
move => aN bN dj.
move: (csum2_pr5 dj)=> cu.
have /equipotent_ex_pr: a \Eq U by apply/card_eqP; rewrite double_cardinal.
have /equipotent_ex_pr: b \Eq V by apply/card_eqP; rewrite double_cardinal.
set gb :=  (equipotent_ex b V); set ga := (equipotent_ex a U).
move =>[qa qb qc][qd qe qf].
pose g x := Yo (x <c a) (Vf ga x) (Vf gb (x -c a)).
pose G := Lf g (a+c b) (U \cup V).
have abN := (NS_sum aN bN).
have sG: source G = a +c b by rewrite/G; aw.
have saab: sub a (a +c b).  
  move => t /(NltP aN) lta; apply/(NltP abN).
  apply:(clt_leT lta (csum_M0le b (CS_nat aN))).
have saG: sub a (source G) by ue.
have fga: function ga by fct_tac.
have fgb: function gb by fct_tac.
have ax: lf_axiom g (a +c b) (U \cup V).
  move => t tab; rewrite /g; Ytac lta.
    by apply: setU2_1; Wtac; rewrite qe; apply/NltP.
  move/(NltP abN): tab => tab.
  move: (NS_lt_nat tab abN) => tN.
  case: (NleT_el aN tN) => // leat.
  rewrite csumC in tab. 
  apply: setU2_2; Wtac; rewrite qb; apply/(NltP bN); apply:cdiff_Mlt => //.
have: bijection G.
  apply: bijective_if_same_finite_c_surj.
      rewrite /G; aw; rewrite  (csum2_pr5 dj) -  (csum2cl U) - (csum2cr _ V).
      rewrite card_card //; fprops.
    by rewrite/G; aw; apply finite_set_nat.
  apply: lf_surjective => //y; case/setU2_P.
    rewrite - qf => /(proj2 (proj2 qd)) [i]; rewrite qe => ia ->.
    by move: (saab i ia) => iab;  ex_tac; rewrite /g  Y_true//; apply/NltP.
  rewrite - qc => /(proj2 (proj2 qa)) [i]; rewrite qb => ia ->.
  move: (NS_inc_nat bN ia) => iN.
  have aux:~ i +c a <c a by apply:cleNgt;apply:(csum_Mle0 i (CS_nat aN)).
  have aux2:  inc (i +c a) (a +c b). rewrite csumC; apply/(NltP abN).
    by apply: (csum_Meqlt aN); apply/(NltP bN).
  ex_tac; by rewrite /g Y_false // cdiff_pr1.
have GU i: inc i a -> (Vf G i) = (Vf ga i).
  move => ia; rewrite /G/g LfV//; last by apply: saab.
  by rewrite /g Y_true//; apply/NltP.
exists G; first by  split => //;rewrite /G; aw.
have fG: function G by fct_tac.
set_extens t.
  move /(Vf_image_P fG saG) => [u ua ->];rewrite (GU _ ua); Wtac.
rewrite - qf; move/(proj2 (proj2 qd)) => [i]; rewrite qe => ia ->.
rewrite -(GU _ ia); apply  /(Vf_image_P fG saG); ex_tac. 
Qed.


Lemma Sperner_16 U: sub U E ->
   exists2 g, bijection_prop g n E & Vfs g (cardinal U) = U.
Proof.
move => suE; set V := (E -s U).
have svE: sub V E. by move => t /setC_P [].
have fsU: natp(cardinal U).
  apply/card_finite_setP;exact: (sub_finite_set suE fsE).
have fsV: natp(cardinal V).
  apply/card_finite_setP;exact: (sub_finite_set svE fsE).
move: (Sperner_15 fsU fsV (set_I2Cr E U)).
by rewrite (setU2_Cr suE) /n (cardinal_setC2 suE) csum2cl csum2cr.
Qed.

Lemma Sperner_17 U V: sub U V -> sub V E ->
  exists2 C, inc C Sperner_mx_chain & (inc U C /\ inc V C). 
Proof.
move => sUV sVE.
move:(sub_smaller sUV) (sub_smaller sVE).
set a := cardinal U; set b := cardinal V; rewrite -/n => leab lebn.
have lean := cleT leab lebn.
have nN:=  Sperner_p0.
have sUE := (sub_trans sUV sVE).
suff: exists g, [/\ bijection_prop g n E, Vfs g a = U & Vfs g b = V].
  move => [g [gA gB gC]]; move: (Sperner_5 gA). 
  move/(NleP nN): lebn => p1; move/(NleP nN): lean => p2. 
  move => Fp; ex_tac; split; apply/funI_P; [  ex_tac | by exists b].
move: (Sperner_16 sUE) => [ga [bga sga tga] ga2].
pose U1 := V -s U; pose V1 := E -s V.
have suE: sub U1 E by move => t /setC_P [/sVE].
have svE: sub V1 E by move => t /setC_P [].
have fsU: natp(cardinal U1).
  apply/card_finite_setP;exact: (sub_finite_set suE fsE).
have fsV: natp(cardinal V1).
  apply/card_finite_setP;exact: (sub_finite_set svE fsE).
have duv1: disjoint U1 V1 by apply: disjoint_pr => x /setC_P [xv _]/setC_P[_ ].
move: (Sperner_15 fsU fsV duv1) => [gb]. 
have eqa: (U1 \cup V1) = E -s U. 
  set_extens t.
    case/setU2_P => /setC_P [ta tb]; apply/setC_P; split; fprops.
  move => /setC_P [tE tU]; case: (inc_or_not t V) => tv.
     by apply: setU2_1; apply/setC_P.
  by apply: setU2_2; apply/setC_P.
have ->: (cardinal U1 +c cardinal V1) = n -c a.
  rewrite csum2cl csum2cr -(csum2_pr5 duv1) eqa cardinal_setC4 //.
rewrite eqa => -[bgb sgb tgb] g2p.
pose h x := Yo (x <c a) (Vf ga x) (Vf gb (x -c a)).
have fga: function ga by fct_tac.
have fgb: function gb by fct_tac.
have aN := NS_le_nat lean nN.
have san :=  (proj33 lean). 
have sbn :=  (proj33 lebn). 
have bN := NS_le_nat lebn nN.
have ax: lf_axiom  h n E.
  rewrite /h => i iin; move:(NS_inc_nat nN iin) => iN.
  case: (NleT_el aN iN) => cia; last by Ytac0; Wtac.
  move/(NltP nN): iin => lin.
  rewrite (Y_false (cleNgt cia)).
  have: inc (i -c a) (source gb).
     rewrite sgb; apply/(NltP (NS_diff a nN)); apply: (cdiff_pr7 cia lin nN).
  by move/ (Vf_target fgb); rewrite tgb => /setC_P;case.
have ha:  sub (cardinal U) (source ga) by ue.
have he y: inc y U -> exists2 i, inc i a & y = h i.
   rewrite - ga2; move/(Vf_image_P fga ha) => [i ia ->]; ex_tac.
   by rewrite /h Y_true //; apply/NltP.
have bgp: bijection_prop (Lf h n E) n E.
  saw;apply: bijective_if_same_finite_c_surj; aw.
     rewrite card_card //; fprops.
   by apply: finite_set_nat.
  apply: (lf_surjective ax) => y yE; case: (inc_or_not y U) => yU.
    move/he:yU =>[i ia ->]; exists i => //; apply: (san _ ia).
  have: inc y (target gb) by rewrite tgb; apply/setC_P.
  move/(proj2 (proj2 bgb)) =>[i]; rewrite sgb => id ->.    
  move: (NS_inc_nat (NS_diff a nN) id) => iN.
  move/(NltP (NS_diff a nN)): id => lin.
  exists (i +c a).
    apply/(NltP nN).
    by move:(csum_Mlteq aN lin); rewrite -{2}(cdiff_pr lean)(csumC a).
  by rewrite /h (Y_false (cleNgt(csum_Mle0 i (CS_nat aN)))) cdiff_pr1.
set gc :=  (Lf h n E).
move: (bgp) => [bgc sgc tgc]; move: (proj1 (proj1 bgc)) => fgc.
have hd i : inc i a ->  inc (Vf ga i) U.
  move => ia;  rewrite - ga2; apply/(Vf_image_P fga ha); ex_tac.
have hb:  Vfs gc a = U.
  have sa:sub a (source (Lf h n E)) by ue.
  set_extens t.
    move/(Vf_image_P fgc sa)  => [u ua ->];  move: (san _ ua) => un.
    by rewrite /h LfV // Y_true; [  apply: hd | apply/NltP].
  move => /he [i ia ->]; apply/(Vf_image_P fgc sa); ex_tac.
  by move: (san _ ia) => un; rewrite LfV.
have hc:  Vfs gc b = V.
  have sb:sub b (source (Lf h n E)) by ue.
  have cu1: cardinal U1 = b -c a.
    by rewrite (cardinal_setC4 sUV) //; apply: (sub_finite_set sVE).
  have aux: (b -c a) <=c (n -c a).
     apply:(csum_le2l aN (NS_diff a bN) (NS_diff a nN)).
     by rewrite (cdiff_pr leab)(cdiff_pr lean).
  have sb1: sub (cardinal U1) (source gb).
    by rewrite sgb cu1; apply: (proj33 aux).
  set_extens t.
    move/(Vf_image_P fgc sb) => [u ub ->]; move: (sbn _ ub) => un;rewrite LfV//.
    rewrite /h; move: (NS_inc_nat bN ub)=> uN; case: (NleT_el aN uN) => cia.
      have sub1v: sub U1 V by move => v /setC_P [].
      rewrite (Y_false (cleNgt cia)); apply: sub1v; rewrite - g2p.
      apply/(Vf_image_P fgb sb1); exists (u -c a) => //; rewrite cu1.
      apply/(NltP (NS_diff a bN)).
      apply:(csum_lt2l aN (NS_diff a uN) (NS_diff a bN)).
      by rewrite (cdiff_pr leab)(cdiff_pr cia); apply/NltP.
    by Ytac0; apply: sUV; apply: hd; apply /NltP.
  move => tV; apply/(Vf_image_P fgc sb); case: (inc_or_not t U) => tU.
    by move /he:tU=> [i ia ->]; exists i;[apply: (proj33 leab)| rewrite LfV//; apply: san].
  have: inc t U1 by apply/setC_P.
  rewrite - g2p => /(Vf_image_P fgb sb1) [u uab ->].
  rewrite cu1 in uab.
  have uN:= NS_inc_nat (NS_diff a bN) uab.
  have ua2: u <c b -c a  by apply/(NltP (NS_diff a bN)).
  have ua3:  inc (u +c a) b.
   by apply /(NltP bN); rewrite- (cdiff_pr leab) csumC; apply:csum_Meqlt.
  have ua4: inc (u +c a) n by apply: sbn.
  by ex_tac; rewrite LfV// /h(Y_false (cleNgt(csum_Mle0 u (CS_nat aN)))) cdiff_pr1.
by exists gc.
Qed.

Lemma Sperner_18 A (k := cardinal A): sub A E ->
  cardinal (Zo (bijections n E) (fun g =>  Vfs g k = A)) =
     factorial k *c (factorial (n -c k)).
Proof.
move => sAE.
have kN: natp k by apply/NatP; apply: (sub_finite_set sAE fsE).
have nN:=  Sperner_p0.
set B :=  (Zo (bijections n n) (fun g => Vfs g k = k)).
set C := Zo _ _.
have lekn: k <=c n by  move: (sub_smaller sAE).
have skn := proj33 lekn.
have ck := proj31 lekn.
move: (Sperner_16 sAE) => [g ga1 ga2].
have: bijection (Lf (compose g) B C).
  move: (ga1) =>[bg sg tg].
  apply: lf_bijective.
  + move => f/Zo_P [/bijectionsP bf fp].
    apply/Zo_P; split; last by rewrite compf_image fp.
    apply/bijectionsP; apply: (compose_bp bf ga1).
  + move => u v /Zo_P [/bijectionsP [bf sf tf] fp].  
    move => /Zo_P [/bijectionsP [bv sv tv] p].
    apply/  (compf_regr bg); split => //; try fct_tac; ue.
  + move => f /Zo_P [/bijectionsP bf fp].
    move:(inverse_bij_bp ga1)(proj1 bg) => ga3 ig.
    have aux: Vfs (inverse_fun g \co f) k = k.
      rewrite compf_image fp - ga2 inverse_direct_image_inj //.
      rewrite  sg; apply: skn.
    move: (bf) =>[bif sf tf].
    exists ((inverse_fun g) \co f).
      apply/Zo_P; split => //; apply/bijectionsP; apply: (compose_bp bf ga3).
    rewrite compf_lK' //; try fct_tac; ue.
move/(card_bijection); aw => <-.
clear C g ga1 ga2.

have s1: sub (n -s k) n by move => t/setC_P [].
have fsn: finite_set n by apply: finite_set_nat.
have fsd := (sub_finite_set s1 fsn).
pose phi1 f := restriction2 f k k.
pose phi2 f := restriction2 f (n-s k) (n -s k).
have rax1 f: inc f B -> restriction2_axioms f k k.
  rewrite /restriction2_axioms. 
  by move => /Zo_P [/bijectionsP[/proj1/proj1 fs -> ->] ->]; split.
have rax2 f: inc f B -> restriction2_axioms f (n -s k) (n -s k).
  rewrite /restriction2_axioms. 
  move => /Zo_P [/bijectionsP[/proj1 [ ff injf] sf tf] Vfk].
  have ha: sub (n -s k) (source f) by ue.
  have hb: sub k (source f) by ue.
  rewrite sf tf; split => // t /(Vf_image_P ff ha) [i lein ->]; apply/setC_P.
  have hc: inc (Vf f i) n by Wtac.
  split => //; rewrite - Vfk =>  /(Vf_image_P ff hb)  [u uk ]. 
  move /(injf i u (ha _ lein) (hb _ uk)) => iu.
  move/setC_P: lein => /proj2; case; ue.
have perm_phi1 f: inc f B -> inc (phi1 f) (permutations k).
  move => fB; move:(rax1 f fB) => ax.
  move: (restriction2_prop ax) => rp2; move: (rp2) =>[fg sg tg].
  move: fB =>/Zo_P [/bijectionsP[ [qa qb] _ _ ] _].
  apply:(permutation_if_inj (finite_set_nat kN) rp2). 
  apply: (restriction2_fi qa ax).
have perm_phi2 f: inc f B -> inc (phi2 f) (permutations (n -s k)).
  move => fB; move:(rax2 f fB) => ax.
  move: fB =>/Zo_P [/bijectionsP[ [qa qb] _ _ ] _].
  move: (restriction2_prop ax) => rp2; move: (rp2) =>[fg sg tg].
  apply:(permutation_if_inj fsd rp2); apply: (restriction2_fi qa ax).
pose phi3 f := J (phi1 f) (phi2 f).
suff: (bijection (Lf phi3 B ((permutations k) \times (permutations (n -s k))))).
   move/card_bijection; aw; rewrite - cprod2_pr1 - cprod2cl - cprod2cr.
   have fsk: finite_set k by apply: finite_set_nat.
   by rewrite (card_permutations fsk)(card_permutations fsd) (card_card ck).
apply: lf_bijective.
+ by move => t tB; apply: setXp_i; [ apply:perm_phi1  |  apply:perm_phi2].
+ move => u v uB vB sphi; move: (pr1_def sphi)  (pr2_def sphi) => eq1 eq2.
  move/Zo_P: (uB) => [ /bijectionsP [[[fu _] _] su tu] uk ].
  move/Zo_P: (vB) => [ /bijectionsP [[[fv _] _] sv tv] vk ].
  apply: function_exten => //; try ue; rewrite su => t itn.
  case: (inc_or_not t k) => tk. 
    move: (rax1 _ uB) (rax1 _ vB) => a1 a2.
    move: (f_equal (Vf ^~ t) eq1). 
    by rewrite (restriction2_V a1 tk)(restriction2_V a2 tk).
  move: (rax2 _ uB) (rax2 _ vB) => a1 a2.
  have tnk: inc t (n -s k) by apply/setC_P.
  move: (f_equal (Vf ^~ t) eq2). 
  by rewrite (restriction2_V a1 tnk)(restriction2_V a2 tnk).
+ move => y /setX_P [py /permutationsP [ba sa ta] /permutationsP [bb sb tb]].
  pose c i := Yo (inc i k) (Vf (P y) i) (Vf (Q y) i).
  move: (proj1(proj1 ba))(proj1(proj1 bb)) => fa fb.
  move: (Vf_target fa); rewrite sa ta => hsa.
  move: (Vf_target fb); rewrite sb tb => hsb.
  have axc: lf_axiom c n n.
    rewrite /c;move => i iin /=; Ytac lik; first by apply: skn; Wtac.
    apply: s1; Wtac; rewrite sb;fprops.
  have ci: injection (Lf c n n).
    apply: (lf_injective axc) => i j iin jin.
    rewrite /c; Ytac lik; Ytac ljk.
    + by move: (proj2 (proj1 ba) i j); rewrite sa; apply.
    + move => eq. 
      have: inc j (n -s k) by apply/setC_P.
      move/ hsb => /setC_P[_]; case; rewrite - eq; exact: (hsa i lik).
    + move => eq. 
      have: inc i (n -s k) by apply/setC_P.
      move/ hsb => /setC_P[_]; case; rewrite  eq; exact: (hsa j ljk).
    + by move: (proj2 (proj1 bb) i j); rewrite sb; apply; apply/setC_P.
  have fci := proj1 ci.
  have fpi: function_prop (Lf c n n) n n by saw.
  have bbcs: inc (Lf c n n) (bijections n n).
    apply:(permutation_if_inj (finite_set_nat nN) fpi ci).
  have aux i:  inc i k ->   Vf (P y) i = Vf (Lf c n n) i.
    by move => ik;move:(skn _ ik) => sin; rewrite LfV// /c; Ytac0.
  have ra: Vfs (Lf c n n) k = k.
    have qa: sub k (source (Lf c n n)) by aw.
    set_extens t.
      move/(Vf_image_P fci qa) => [u uk]; move: (skn _ uk) => un.
      rewrite LfV//; move ->; rewrite /c; Ytac0; Wtac.
    move => tk; apply/(Vf_image_P fci qa).
    have tim: inc t (target (P y)) by ue.
    move: ((proj2 (proj2  ba)) _ tim); rewrite sa; move => [i ik ->]; ex_tac.
  have cB :inc (Lf c n n) B by apply/Zo_P.
  have pp1:  P y = phi1 (Lf c n n).
    move: (perm_phi1 _ cB)(rax1 _ cB) => /permutationsP [[[fc _] _] sc tc] ax.
    apply: function_exten=> //; try ue; rewrite sa => i ik.
    by rewrite /phi1 restriction2_V //; apply: aux.
  have pp2: Q y = phi2 (Lf c n n).
    move: (perm_phi2 _ cB)(rax2 _ cB) => /permutationsP [[[fc _] _] sc tc] ax.
    apply: function_exten=> //; try ue; rewrite sb => i ik.
    rewrite /phi1 restriction2_V //; move/setC_P: ik =>[qa qb].
    by rewrite LfV///c; Ytac0.
  exists (Lf c n n); first by apply/Zo_P; split.
  rewrite/phi3;apply: pair_exten; aww.
Qed. 

Lemma nb_permutations_nat m: natp m -> cardinal (permutations m) = factorial m.
Proof.
move => mN; rewrite card_permutations.
  by rewrite (card_card(CS_nat mN)).
by apply: finite_set_nat.
Qed.

Lemma Sperner_19 A (k := cardinal A):
  sub A E -> 
  cardinal (Zo Sperner_mx_chain (inc A))
  = factorial k *c (factorial (n -c k)).
Proof.
move => sAE.
rewrite -(Sperner_18 sAE).
pose F g := fun_image (csucc n) (Vfs g).
move: (sub_smaller sAE); rewrite -/k -/n => lekn.
have nN:=  Sperner_p0.
have kN := (NS_le_nat lekn nN).
set W := Zo _ _; set V := Zo _ _; suff: bijection (Lf chain_of_fun  V W).
  by move/card_bijection; aw.
apply: lf_bijective.
-  move => g /Zo_P [/bijectionsP bgp gc].
  move:(Sperner_5 bgp) => h.
  by apply/Zo_P; split => //; apply/funI_P; exists k => //; apply/NleP.  
- by move => u v /Zo_S/bijectionsP uu /Zo_S/bijectionsP vv; apply:Sperner_13.
- move => t /Zo_P [/Sperner_10] [ bgp ->] /funI_P [i lin Ai].
  set g:= Lf _ _ _.
  have axa: k = i.
    move/(NleP nN): lin bgp=> [ci _ ssin]  [[qa _] sg tg].
    by rewrite /k Ai cardinal_image ? sg // (card_card ci).
  by exists g => //; apply/Zo_P; split; [ apply/bijectionsP | ue ].
Qed. 

Definition free_rep f :=
  [/\ bijection f, natp (source f) & inc (target f) (free_subsets r)].
Definition chain_free_meet f C := 
  union(Zo (csucc (source f)) (fun i => \0c <c i /\ inc (Vf f (cpred i)) C)). 
Definition chain_free_meet_i f i :=
  Zo Sperner_mx_chain (fun C => chain_free_meet f C  = i).

Lemma free_rep_prop1 A: inc A  (free_subsets r) ->
   exists2 f, free_rep f & target f = A.
Proof.
move => h.
move:(h) => /Sperner_p4/proj1/sub_smaller;  rewrite card_setP- cpowcr => h'.
move: (NS_le_nat h' (NS_pow NS2 Sperner_p0)) => caN.
case: (equipotent_ex_pr1(double_cardinal A)).
set f := equipotent_ex _ _; move => bf sf tf.
exists f => //; split => //; ue.
Qed.

Lemma free_rep_prop2 f : free_rep f ->
 cardinal (source f) = cardinal (target f).
Proof. by move => [fp _ _]; apply: card_bijection. Qed.

Lemma Sperner_cf0 f i: free_rep f -> inc i (source f) ->
   [/\  sub (Vf f i) E, cardinal  (Vf f i) <=c n & natp (cardinal (Vf f i))].
Proof.
move: Sperner_p0 => nN fp isf.
have sE: sub (Vf f i) E.
  move:fp =>[ qa qb /Sperner_p4/proj1  qc]. 
  by move /setP_P: (qc _ (Vf_target (proj1(proj1 qa)) isf)).
move: (sub_smaller sE) => le1.
split => //; apply/(NS_le_nat le1 nN).
Qed.

Lemma Sperner_cf1 f C i: free_rep f -> inc C Sperner_mx_chain ->
  inc i (source f) -> inc (Vf f i) C -> chain_free_meet f C = csucc i.
Proof.
move => [[[ff fi] _] sfN rrf] Cp lin h.
rewrite /chain_free_meet; set T := Zo _ _.
suff: T = singleton (csucc i) by move ->; rewrite setU_1.
move: (Vf_target ff lin) => pa.
move: (NS_inc_nat sfN lin) => iN.
apply: set1_pr.
   apply: (Zo_i); first by apply/(NleP sfN)/(cleSltP iN) /(NltP sfN).
   rewrite (cpred_pr2 iN); split => //; apply: succ_positive.
move => j /Zo_P [jsf [jn0 jp]].
move: (NS_inc_nat (NS_succ sfN) jsf) => jN.
move: (cpred_pr jN (nesym (proj2 jn0)))=> [kN kv].
have ksf: inc (cpred j) (source f).
  apply/(NltP sfN)/(cleSltP kN)/(NleP sfN);ue.
have vtt: inc (Vf f (cpred j)) (target f) by  Wtac.
rewrite kv; apply: f_equal.
move/Zo_P: Cp => [/total_subordersP [C1 [_ C3]] _].
move: (subp_osr E) => [or sr].
move: (C3 (Vf f i) (Vf f (cpred j))); rewrite iorder_sr // => h1.
move/Zo_P: rrf => [ _ h2].
case: (h1 h jp) => /iorder_gle1 cp.
  by move: (fi _ _ lin ksf (h2 _ _  pa vtt cp)).  
by move: (fi _ _ ksf lin (h2 _ _  vtt pa cp)).
Qed.

Lemma Sperner_cf2 f C: free_rep f -> inc C Sperner_mx_chain ->
  (forall  i, inc i (source f) -> ~inc (Vf f i) C) -> 
  chain_free_meet f C = \0c.
Proof.
move =>  [[[ff fi] _] sfN rrf]  hb hc.
rewrite /chain_free_meet; set T := Zo _ _.
suff: T = emptyset by move ->; rewrite setU_0.
apply/set0_P => j /Zo_P [jsf [jp jc]].
move: (NS_inc_nat (NS_succ sfN) jsf) => jN.
move: (cpred_pr jN (nesym (proj2 jp)))=> [kN kv].
have ksf: inc (cpred j) (source f).
  apply/(NltP sfN)/(cleSltP kN)/(NleP sfN);ue.
exact: (hc _ ksf jc).
Qed.

Lemma Sperner_cf3 f C: free_rep f -> inc C Sperner_mx_chain ->
  chain_free_meet f C = \0c \/
  exists i,  [/\ inc i (source f), inc (Vf f i) C &
    chain_free_meet f C = (csucc i)].
Proof.
move => fp Cp.
case: (p_or_not_p (forall  i, inc i (source f) -> ~inc (Vf f i) C)) => h.
  left;exact:(Sperner_cf2 fp Cp h).
have [i isf fii]: (exists2 i, inc i (source f) & inc (Vf f i) C).
  ex_middle bad; case: h => i ha hb; case bad; ex_tac.
move: (Sperner_cf1 fp Cp isf fii) => aux.
by right; exists i.
Qed.

Lemma Sperner_cf4 f (p := source f): free_rep f ->
   factorial n = csumb (csucc p) (fun i => cardinal (chain_free_meet_i f i)).
Proof.
move => fp.
rewrite - csum_pr4_bis; last first.
  move => i j ip jp; mdi_tac nij => x /Zo_hi iv /Zo_hi jv; case: nij; ue.
rewrite - Sperner_14; congr cardinal. 
set_extens t; last by move =>/setUf_P [y yp] /Zo_S.
move => tC; apply/setUf_P.
have pN: natp p by case: fp.
have zp: inc \0c (csucc p) by apply/(NleP pN); apply: cle0n.
case: (Sperner_cf3 fp tC); first by  move => h; ex_tac; apply:Zo_i.
move => [i [isf pb pc]].
move/(NltP pN): isf => lip; move: (NS_lt_nat lip pN) => iN.
have sisip : inc (csucc i) (csucc p) by apply/(NleP pN)/cleSltP.
by ex_tac; apply: Zo_i.
Qed.

Lemma Sperner_cf5 f (p := source f)
      (m := fun i => cardinal (chain_free_meet_i f i)):
  free_rep f ->
   cn *c factorial n = cn *c (m \0c) +c 
     csumb p (fun i => cn *c (m (csucc i))).
Proof.
move => h; rewrite(f_equal (cprod2 cn) (Sperner_cf4 h)).
have pN: natp p by case: h.
have zi: inc \0c (csucc p) by apply/(NleP pN); apply: cle0n.
rewrite cprod2Dn (fct_sum_rec1 _ pN); aw; rewrite csumC.
by apply: f_equal; apply: csumb_exten => i isf; aw.
Qed.

Lemma Sperner_cf6 f i: free_rep f -> inc i (source f) ->  
   chain_free_meet_i f (csucc i) = (Zo Sperner_mx_chain (inc (Vf f i))).
Proof.
move => fp mip.
have aux k: inc k (source f) -> cardinalp  k.
   move => ik; exact (CS_nat (NS_inc_nat (proj32 fp) ik)).
set_extens t => /Zo_P [qa qb]; apply/Zo_P; split => //.
  case:(Sperner_cf3 fp qa); rewrite qb; first by move => qd;case:(@succ_nz i).
  by move =>[j [/aux jsf fj]] /(csucc_inj (aux _ mip) jsf) => ->.
by  move: (Sperner_cf1 fp qa mip qb).
Qed.
  
Lemma Sperner_cf7 f i (a := cardinal (Vf f i))
      (m := cardinal (chain_free_meet_i f (csucc i))):
  free_rep f -> inc i (source f) -> 
  natp m /\ m = factorial a *c factorial (n -c a).
Proof.
move => fp isf; move: (Sperner_cf0 fp isf) =>[sE _ aN].
rewrite /m (Sperner_cf6 fp isf)  (Sperner_19 sE); split => //.
apply: NS_prod; apply:NS_factorial => //; apply: (NS_diff _ Sperner_p0).
Qed.

Lemma csum2_compare_spec a b s : natp a -> natp b -> s = a +c b ->
   a <=c s /\ (a = s -> b = \0c).
Proof.
move => aN bN ->; split.
  exact: (csum_M0le b (CS_nat aN)).
by rewrite -{1}(csum0r (CS_nat aN));  move/(csum_eq2l aN NS0 bN).
Qed.

Lemma Sperner_cf8 f (p := source f)
      (m := fun i => cardinal (chain_free_meet_i f i))
      (s := csumb p (fun i => cn *c (m (csucc i)))):
  free_rep f ->
   [/\ natp s, p *c factorial n <=c s &
   (p *c factorial n = s -> 
         forall i, inc i p -> cn *c m (csucc i) = factorial n)].
Proof.
move => fp.
have nN := Sperner_p0.
pose a i := cn *c m (csucc i); pose b i := a i -c  factorial n.
have ncN: natp cn by apply: (NS_binom nN (NS_half _)).
have bN i: inc i p -> natp (b i).
  by move/(Sperner_cf7 fp) => /proj1 h; apply: NS_diff; apply: NS_prod.
have aux i: inc i p -> factorial n  +c b i =  a i.
  move => ip; apply: cdiff_pr.
  rewrite /a /m(proj2 (Sperner_cf7 fp ip)); apply:(Sperner_b1 nN).
  move:fp =>[/proj1/proj1 ff _ /Sperner_p4/proj1 h ].
  by move:(h _ (Vf_target ff ip)) => /setP_P/sub_smaller.
have eq1: s = p *c factorial n +c csumb p b.
  rewrite cprodC - csum_of_same (sum_of_sums _ b p).
  by apply: csumb_exten => i lip; rewrite (aux _ lip).
have pN:= (proj32 fp).
have fN := (NS_factorial nN).
have p1N: natp (p *c factorial n). apply: (NS_prod  pN fN).
have p2N:  natp (csumb p b).
  have fsp := (finite_set_nat pN).
  apply:finite_sum_finite; split; rewrite /allf;aw; trivial.
  move => i ip; rewrite LgV//; exact: (bN _ ip).
have  sN: natp s by rewrite eq1; apply: (NS_sum).
move: (csum2_compare_spec p1N p2N eq1) =>[ea eb]; split => // ec i ip.
move /csum_zero_unit_bis : (eb ec) => h; move: (h i); aw; rewrite LgV// => h1.
by move: (aux _ ip); rewrite -/(b i) (h1 ip) (csum0r (CS_nat fN)).
Qed.

Lemma Sperner_cf9 f : free_rep f -> (source f) <=c cn.
Proof.
move => fp.
move: (Sperner_cf5 fp)(Sperner_cf8 fp).
set c1 := (cn *c cardinal  _); set c := csumb _ _ => eq1 /proj32 le1.
have cc: cardinalp c by rewrite /c/csumb/ csum; fprops.
have nN := Sperner_p0.
move: (cleT le1 (csum_Mle0  c1 cc)); rewrite - eq1  => h.
have ncN: natp cn by apply: (NS_binom nN (NS_half _)).
exact:(cprod_le2r (NS_factorial nN) (proj32 fp) ncN  (factorial_nz nN) h).
Qed.

Lemma Sperner_20 A: inc A  (free_subsets r) -> cardinal A <=c cn.
Proof.
move / free_rep_prop1 => [f fp <-]; move: (Sperner_cf9 fp) => le1.
by rewrite - (card_bijection (proj31 fp)) (card_nat (proj32 fp)).
Qed.

Lemma Sperner_21 : order_width r  cn.
Proof.
split; last exact: Sperner_20.
move: Sperner_p0 => nN.
move: (cle_halfn_n nN) => lehn.
move: (Sperner_p2 lehn)  (Sperner_p5 lehn) => p1 p2.
ex_tac.
Qed.

Lemma Sperner_cf11 f : free_rep f -> (source f) = cn ->
  (forall C, inc C Sperner_mx_chain -> 
     exists2 i, inc i (source f) & inc (Vf f i) C) /\
  (forall i, inc i (source f) -> is_half_n n  (cardinal (Vf f i))).
Proof.
move => fp cs.
have nN := Sperner_p0.
move: (Sperner_cf5 fp)(Sperner_cf8 fp).
set c1 := (cn *c cardinal  _); set c := csumb _ _ => eq1 [cN le1 hp].
have ncN: natp cn by apply: (NS_binom nN (NS_half _)).
have cc: cardinalp c by apply: CS_nat.
have cc1: cardinalp c1 by apply: CS_prod2.
have sN: natp (c1 +c c) by rewrite - eq1;apply:(NS_prod ncN (NS_factorial nN)).
have c1N:=(NS_in_suml cc1 sN).
rewrite csumC in eq1.
move: (csum2_compare_spec cN c1N eq1) => [qa qb].
have c1z : c1 = \0c.
  by apply:qb; apply:cleA => //; move: le1; rewrite cs eq1.
have cnz: cn <> \0c by apply: (binom_pr3 nN (NS_half nN) (cle_halfn_n nN)).
split.
  move => C Cp.
  case: (cprod2_eq0 c1z) => // /card_nonempty xfmz.
  case: (Sperner_cf3 fp Cp) => cp; first by empty_tac1 C; apply/Zo_P.
  move:cp => [i [isf iv _]]; ex_tac. 
have /hp T: source f *c factorial n = c by rewrite cs eq1 c1z (csum0r cc).
move=> i ip; move: (T i ip). rewrite (proj2 (Sperner_cf7 fp ip)) => /esym  av.
have /sub_smaller lan: sub (Vf f i) E.
  move:fp =>[ qe _ /Sperner_p4/proj1  qc]. 
  by move /setP_P: (qc _ (Vf_target (proj1(proj1 qe)) ip)).
exact: (Sperner_b2 nN lan av).
Qed.


Lemma Sperner_cf12 f k (F  := (subsets_with_p_elements k E)):
 free_rep f -> (source f) = cn -> k <=c n ->  is_half_n n k ->
  sub (target f)  F -> target f =  F.
Proof.
move:Sperner_p0  => nN fp csf lekn hn stf.
have ncN: natp cn by apply: (NS_binom nN (NS_half _)).
move: (fp) => [bf qa qb].
have cf: (cardinal F) = cn.
  by rewrite /F(Sperner_p2 lekn);move/ (binom_monotone_max_arg nN lekn): hn.
have cc:  target f =c F.
  by rewrite - (card_bijection bf) csf cf (card_card (CS_nat ncN)). 
  have ha: finite_set F by apply/NatP; rewrite cf.
exact: (cardinal_setC5 ha stf cc).
Qed.

Lemma Sperner_cf13 f (F  := (subsets_with_p_elements (chalf n) E)):
 free_rep f -> source f = cn -> evenp n -> target f =  F.
Proof.
move :Sperner_p0 => nN fp sg en.
move: (proj2(Sperner_cf11 fp sg)) => H.
have aux: is_half_n n (chalf n)by left.
apply: (Sperner_cf12 fp sg  (cle_halfn_n nN) aux).
move: (fp) => [[injp [_ sj]] cf /Sperner_p4/proj1 ste].
move => i itf; apply /Zo_P; split; first by move: (ste _ itf).
move: (sj _ itf) =>[k kf ->];case: (H _ kf) => // dv.
move: (Sperner_cf0 fp kf) =>[_ q1 q2].
move: (cdiff_pr q1); rewrite dv {2} (half_even en) /cdouble - csum_nn.
apply:(csum_eq2r (NS_half nN) q2  (NS_half nN)).
Qed.

Lemma Sperner_cf14 f (F := fun k => (subsets_with_p_elements k E)):
 free_rep f -> source f = cn -> oddp n -> 
 target f =  F (chalf n) \/ target f =  F (csucc (chalf n)).
Proof.
move => fp sg on.
have hN := NS_half (proj1 on).
move: (Sperner_cf11 fp sg) => [Ha Hb].
move: (half_odd on); 
  rewrite /cdouble - csum_nn - (csum_Sn _ hN); set q := chalf n => nv.
pose a i :=  cardinal (Vf f i).
have ap i: inc i (source f) ->  a i = q \/ a i = csucc q.
  move => isf; move: (Sperner_cf0 fp isf) => [_ lean aN].
  case: (Hb _ isf); [by left | move => eq ; right].
  apply:(csum_eq2r hN aN  (NS_succ hN)).
  by move: (cdiff_pr lean); rewrite eq {2} nv. 
move: (fp) => [[[ffp injp] [_ sj]] cf /Sperner_p4[ste tff]].
case: (p_or_not_p (exists2 i, inc i (source f) & a i = q)); last first.
  have le1: csucc q <=c n by rewrite nv; apply: csum_M0le; fprops.
  have le2:  is_half_n n (csucc q). 
    right; rewrite {1} nv csumC; apply: cdiff_pr1; fprops.
  move => bad ; right; apply: (Sperner_cf12 fp sg le1 le2). 
  move => t tf; apply/ Zo_P;split; first by move: (ste _ tf).
  move: (sj _ tf) =>[k kf ->].  case: (ap _ kf) => // dv.
  ex_middle bad1; case: bad; ex_tac.
have nN := proj1 on.
move => [i0 i0sg ai0v]; left.
have le1: q <=c n by apply cle_halfn_n. 
have le2: is_half_n n q by left.
apply: (Sperner_cf12 fp sg le1 le2). 
move => t tf; apply/ Zo_P;split; first by move: (ste _ tf).
move: (sj _ tf) =>[k kf kv]; rewrite kv;case: (ap _ kf) => //.
rewrite /a - kv => ct.
set U := (Vf f i0).
have Utf: inc U (target f) by rewrite /U;  Wtac.
have cU: cardinal U = q by [].
have H A p: cardinalp p -> cardinal A = csucc p -> exists B x,
   [/\ A = B +s1 x, cardinal B = p, sub B A & B <> A]. 
   move => qN cA. 
   case: (emptyset_dichot A) => Ae.
     by case: (@succ_nz p); rewrite - cA Ae cardinal_set0.
   move: (rep_i Ae) => rt; exists (A -s1 (rep A)), (rep A).
   move:(csucc_pr2 rt); rewrite cA.
   move/ (csucc_inj qN (CS_cardinal _)) => <-.
   rewrite (setC1_K rt); split => //b; first by move/setC1_P; case.
   by move: rt; rewrite - {2} b => /setC1_P [_] [].
move: (H _ _  (proj31 le1) ct) => [V [x0 [ra cV rv]]]; case.
have stE: sub t E by  apply/setP_P; apply: ste.
have sVE := (sub_trans rv stE).
suff tV: (inc V (target f))  by apply: (tff V t tV tf); apply/subp_gleP.
have pN: natp (cardinal (V -s U)).
  by apply/NatP; apply: sub_finite_set fsE => x /setC_P [/sVE].
suff: forall p, natp p -> forall V, sub V E -> cardinal (V -s U) = p ->
     cardinal V = q -> inc V (target f).
   by move => hyp; apply: (hyp _ pN V sVE). 
clear V  cV t tf k kf kv ct ra rv sVE stE x0 pN.
apply: Nat_induction.
  have fsU: finite_set U by apply/NatP; rewrite cU. 
  move => V sVE /card_nonempty/empty_setC cdz cvq.
  by rewrite - cU in cvq; rewrite (cardinal_setC5 fsU cdz cvq).
move => p pN  Hrec V Ve cvd cvq.
move: (H (V -s U) p (CS_nat pN) cvd) => [W [x1 [pa pb pc pd]]].
case: (emptyset_dichot (U -s V)) => nes.
   have fsV: finite_set V by apply/NatP; rewrite cvq. 
   by rewrite - cvq in cU; rewrite -(cardinal_setC5 fsV (empty_setC nes) cU).
move /setC_P: (rep_i nes); set y := rep (U -s V);move =>[yU yV].
have yE: inc y E by move /setP_P: (ste _ Utf); apply.
have sW: sub W (V -s U) by rewrite pa => x xW; fprops.
move: (setU1_1 W x1); rewrite - pa => /setC_P[x1V x1U].
pose W1 := W \cup (U\cap V).
pose V' := W1 +s1 y.
case: (inc_or_not x1 W) => ixw.
  by case: pd; rewrite pa; symmetry;apply:setU1_eq.
have eq3: V +s1 y = V' +s1 x1.
  set_extens z; case/setU1_P.
  + move => zV; apply/setU1_P.
    case: (equal_or_not z x1) => zx1; [by right | left; apply/setU1_P].
    left;apply/setU2_P; case: (inc_or_not z U) => zU; first by right; fprops.
    by move:(setC_i zV zU); rewrite pa => /setU1_P; case => zv //; left.
  + move->; apply: setU1_r; apply:setU1_1.
  + case/setU1_P; [ case/setU2_P; last move => /setI2_P [] | move ->];fprops.
    by move => /sW/setC_P [zW _]; apply: setU1_r.
  + by move ->; apply: setU1_r.
have ixV: ~ (inc x1 V').
  case/setU1_P; first by case/setU2_P => // /setI2_P [ x1v]; case: x1U.
  by  move => ex1y; case: yV; rewrite - ex1y.
have cardV': cardinal V' = q.
  move: (f_equal cardinal eq3); rewrite (csucc_pr ixV)  (csucc_pr yV) - cvq.
  move => h;symmetry; apply:csucc_inj; fprops.
have svE: sub V' E.
  move => x /setU1_P; case; last by move ->.
  by case/setU2_P; [ move=> /pc /setC_P [/Ve] | case/setI2_P => _ /Ve ].
have sWE:= (setU1_sub Ve yE).
have eq1: V' -s U = W.
  set_extens x.
    case/setC_P; case/setU1_P;first by case/setU2_P => // /setI2_P [].
    by move ->; case.
  move => xW;move: (sW _ xW) => /setC_P [qa qb].
  by apply /setC_P; split => //; apply/setU1_P; left; apply/setU2_P; left.
move: pb; rewrite - eq1 => cV'.
move:(Hrec V' svE cV' cardV') => V'tf.
move: (Sperner_17 (@sub_setU1 V y) sWE) =>[C Cp [i1 i2]].
move: (Ha C Cp) => [j jsf fjC].
move/Zo_S: (Cp) => /Sperner_3 cij.
have Wt: inc (Vf f j) (target f) by Wtac.
case : (ap _ jsf) => cfj.
   have xx:V =c Vf f j by ue.
   by rewrite (cij V (Vf f j) i1 fjC xx). 
have xx:  (V +s1 y) =c Vf f j by rewrite (csucc_pr yV) cvq - cfj.
move: Wt; rewrite - (cij _ (Vf f j) i2 fjC xx) eq3 => vtf.
have bad: gle r V' (V' +s1 x1) by apply/subp_gleP; split; fprops; ue.
case: ixV; rewrite (tff V'(V' +s1 x1) V'tf vtf bad); fprops.
Qed.


Lemma Sperner_cf15 f (F := fun k => (subsets_with_p_elements k E)):
  free_rep f -> source f = cn ->
  exists k, [/\ natp k, is_half_n n k &  target f = F k].
Proof.
move => ha hb.
have nN:= Sperner_p0.
move: (NS_half nN) => hN; move: (NS_succ hN) => shN.
have:  is_half_n n (chalf n) by left.
case: (p_or_not_p  (evenp n)) => en.
  by exists (chalf n); rewrite (Sperner_cf13 ha hb en).
have on: oddp n by [].
case:(Sperner_cf14 ha hb on) => ->; first by exists (chalf n).
exists (csucc (chalf n)); split => //.
right; rewrite {1} (half_odd on)  /cdouble - csum_nn - (csum_nS _ hN).
by apply: (cdiff_pr1).
Qed.

Lemma Sperner_22 A: inc A  (free_subsets r) -> cardinal A = cn ->
  exists k, [/\ natp k, is_half_n n k & A = subsets_with_p_elements k E].
Proof.
move / free_rep_prop1 => [f fp <-]; move: (Sperner_cf15 fp).
rewrite - (card_bijection (proj31 fp)) (card_nat (proj32 fp)); apply.
Qed.

Lemma Lubell_Yamamoto_Meshalkin A
   (b := fun k => cardinal (Zo A (fun z => cardinal z = k))):
  (inc A (free_subsets r)) ->
  csumb (csucc n) (fun k => (b k) *c ((factorial k) *c (factorial (n-c k))))
   <=c factorial n.
Proof.
move/free_rep_prop1 => [f frp tf].
pose c k:= (factorial k) *c (factorial (n-c k)).
pose a i := cardinal (Vf f i).
pose m i := cardinal (chain_free_meet_i f (csucc i)).
move: (frp) => [bf pN /free_subsetsP/proj1 sts].
move:  (Sperner_cf4 frp); rewrite (fct_sum_rec1 _ pN).
set s1 := csumb _ _; set s2 := cardinal _; move => eq1.
have cs1: cardinalp s1 by apply: CS_cardinal.
set s3 := csumb _ _.
move: (@csum_M0le s1 s2 cs1); rewrite - eq1; clear s2 eq1 cs1.
suff: s1 = s3 by move ->.
transitivity ( csumb (source f) (fun i =>  c (a i))).
  apply: csumb_exten => i iip.
  by rewrite (proj2 (Sperner_cf7 frp iip)).
have cb t: inc t A ->  inc (cardinal t) (csucc n).
  rewrite -tf; move => /sts tA; apply/(NleP (Sperner_p0)).
  by move:tA; rewrite (proj2 (subp_osr E)) => /setP_P /sub_smaller.
move: (proj1(proj1  bf)) => ff.
pose X := Lg A (fun i => c (cardinal i)).
have ha: target f = domain X by rewrite /X; aw.
transitivity (csum (X \cf graph f)).
  rewrite /composef (domain_fg ff); apply: csumb_exten.
  move => i isf; rewrite /X -/(Vf f i) LgV//; Wtac.
pose g k := Zo A (fun z  => cardinal z = k).
have pfg: partition_w_fam (Lg (csucc n) g) (domain X).
  rewrite - ha tf; split.
  - fprops.
  - hnf; aw;move => u v isn vsn; rewrite !LgV//; mdi_tac ww.
    by move => t /Zo_P [_ ct] /Zo_P [_ ct']; case:ww; rewrite - ct ct'.
  - set_extens t.
       by move => /setUb_P; aw; move => [y ysb]; rewrite !LgV//; move/Zo_S.
   move => tA; move: (cb t tA) => cc;apply/setUb_P; aw; ex_tac; rewrite LgV//.
     by apply:Zo_i.
rewrite - (csum_Cn ha bf) (csum_An pfg); aw; apply: csumb_exten=> i lin /=.
rewrite LgV// cprodC cprod2cr -/(g i) - csum_of_same; apply: csumb_exten.
move => k /Zo_P [kA <-]; rewrite /X LgV//.
Qed.

End Sperner.



Lemma Exercise4_5a Y T k:
  cardinal Y = k -> cardinal T = k -> natp k ->
  sub T (union Y) -> disjoint_set Y ->
  (forall Z, inc Z Y -> small_set (T \cap Z)) ->
  (forall Z, inc Z Y -> singletonp (T \cap Z)).
Proof.
move => cY cT kN Tu ald als.
pose f x:= select (fun z => inc x z) Y.
have Ha x: inc x T -> inc x (f x) /\ inc (f x) Y.
  move => xT; apply: select_pr.
     move /setU_P: (Tu _ xT)=> [y ya yb]; ex_tac.
  move => a b /= aY xa bY xb; case: (ald a b aY bY) => // dab; empty_tac1 x.
have awx: lf_axiom f T Y by move => a /Ha [].
have Hb a b: inc a T -> inc b T -> f a = f b -> a = b.
   move => aT bT eq1; move: (Ha _ aT)(Ha _ bT)=> [qa qb][qc qd].
   rewrite eq1 in qa qb.
   exact:(als _ qd a b  (setI2_i aT qa)  (setI2_i bT qc)).
set g := (Lf f T Y).
have tg: target g = Y  by rewrite /g ;aw.
have sg: source g = T  by rewrite /g ;aw.
have stgc:source g =c target g by rewrite sg tg cY cT.
have fsg: finite_set (source g) by rewrite sg; apply /NatP; rewrite cT.
have ig : injection g by apply: lf_injective => // a /Ha [].
move: (bijective_if_same_finite_c_inj stgc fsg ig) => bg. 
move => Z ZY; apply/singletonP; split; last exact: (als _ ZY).
rewrite - tg in ZY.
move: (proj2 (proj2 bg) _ ZY) => [x];rewrite  sg /g => xs; rewrite LfV// => ->.
move: (proj1 (Ha _ xs)) => xz; exists x; fprops.
Qed.

Definition Exercise4_5_conc r k :=
  exists X, [/\ partition_s X (substrate r), cardinal X = k &
    sub X (total_suborders r)].


Lemma Exercise4_5b_alt r k: finite_set (substrate r) ->
  order r -> natp k ->  order_width r k -> Exercise4_5_conc r k.
Proof.
move /NatP; set n := cardinal (substrate r).
move: (refl_equal n); rewrite {2} /n.
move: n; move=> n nc nN; move: n nN r k nc; apply: Nat_induction1.
move=> n nN hrec r k csr or kN [[X Xf cX] h2].
have fsr: finite_set(substrate r) by apply/NatP; ue.
move: (order_length_exists fsr); set ol:= the_order_length _.
move => [olN oln [[C /total_subordersP [Csr Ctot]cC] olb]].
have dots u v: gle r u v ->  inc (doubleton u v) (total_suborders r).    
  move=> luv; move: (arg1_sr luv) (arg2_sr luv) => usr vsr.
  set Y := doubleton u v.
  have sY: sub Y (substrate r) by apply: sub_set2.
  apply:(total_suborder_prop or sY) => a b /set2_P [] -> /set2_P [] ->.
  - by left; order_tac.
  - by left.
  - by right.
  - by right; order_tac.
case: (NleT_el NS2 olN) => ol2; last first.
  move: (greatest_is_partition (substrate r)). 
  set A := greatest_partition _ => h.
  have cA: cardinal A = cardinal (substrate r). 
    by apply: (cardinal_fun_image) => i j _ _; apply:set1_inj.
  have At: sub A (total_suborders r).
    move => t /funI_P[z zsr ->]; apply:(total_suborder_prop or (set1_sub zsr)).
    by move => a b /set1_P -> /set1_P ->; left; order_tac.
  have /h2 le1: inc (substrate r) (free_subsets r).
    apply/free_subsetsP; split => // u v usr vsr luv; ex_middle bad.
    move: (dots _ _ luv).
    by move/olb; rewrite (cardinal_set2 bad) => /cleNgt; case.
  exists A; split => //; rewrite cA; apply: cleA => //.
  by move/free_subsetsP: Xf => [/sub_smaller]; rewrite cX.
move: (iorder_osr or Csr) => [orC sioC].
have fsC: finite_set (substrate (induced_order r C)). 
  by rewrite sioC; apply /NatP; ue.
have neC: nonempty (substrate (induced_order r C)). 
  rewrite sioC; apply /cle1P; rewrite cC; exact: (cleT cle_12 ol2).
move: (finite_set_torder_least Ctot fsC neC) =>[alpha []].
move: (finite_set_torder_greatest Ctot fsC neC) => [omga []].
rewrite sioC => oC oop aC aap.
have olC x: inc x C -> gle r x omga by move/oop/ iorder_gle1.
have alC x: inc x C -> gle r alpha x by move/aap/ iorder_gle1.
move:(alC _ oC) => lab.
case: (equal_or_not alpha omga) => nab.
   have cv : C = singleton alpha .
     apply :set1_pr => // x xC; move: (olC _ xC) (alC _ xC); rewrite - nab.
     move => qa qb; order_tac.
   move: (cardinal_set1 alpha); rewrite - cv cC=> ea.
   case: (cleNgt ol2); rewrite ea; exact: (clt_12).
have ltab: glt r alpha omga  by split.
move: (arg1_sr lab) (arg2_sr lab) => aE oE.
clear oop aap lab nab.
pose E' := (substrate r) -s (doubleton alpha omga).
have sub1: sub E' (substrate r) by move => t /setC_P [].
move: (iorder_osr or sub1); set r1:= induced_order _ _; move =>[or1 sr1].
have fs1: finite_set (substrate r1).
  by rewrite sr1; apply: (sub_finite_set sub1 fsr).
move: (order_width_exists fs1); set k1 := the_order_width _.
move => [k1N kbd owrk1]; move: (owrk1)  => [[X1 cX1 x1p] k1max].
move/free_subsetsP: cX1 => [X1sr X1free]. 
have Xfree a b: inc a X1 -> inc b X1 -> gle r a b -> a = b.
  move => ax bx le; apply:(X1free a b ax bx);apply/iorder_gleP.
  by split => //; rewrite - sr1; apply: X1sr.
have le1: k1 <=c k.
  suff: inc X1 (free_subsets r) by move/ h2; rewrite x1p.
  apply/free_subsetsP.
  split; first by apply: (sub_trans X1sr); rewrite sr1.
  by move => u v ux1 vx1 le1; apply:(Xfree u v ux1 vx1). 
have: k = k1 \/ k = csucc k1.
  set X2 := X \cap E'.
  have sr2: sub X2 (substrate r1) by rewrite sr1 => t /setI2_P [].
  move/free_subsetsP: Xf => [qa qb].
  have: inc X2 (free_subsets r1).
    apply/free_subsetsP; split => // u v /setI2_P [uX _] /setI2_P[vX _].
    by move/iorder_gle1; apply:qb.
  move/k1max => le2. 
  have aux: cardinal X = csucc (cardinal X2) ->  k = k1 \/ k = csucc k1.
     move => h.
     case: (equal_or_not k1 k) =>kk1; [ by left | right].
     have: k1 <c k by split.
     by move/(cleSltP k1N); apply: cleA; move: (cleSS le2); rewrite - cX - h.
  case: (inc_or_not alpha X)=> hb; case: (inc_or_not omga X) => ha.
  - case: (proj2 ltab); exact: (qb _ _ hb ha  (proj1 ltab)).
  -  apply: aux.
     have ->: X = X2 +s1 alpha.
       set_extens t; last by case/setU1_P; [ case/setI2_P | move ->].
       move => tx; apply/setU1_P;  case: (equal_or_not t alpha).
         by move ->; right.
       move => ta; left; apply/setI2_P; split => //; apply/setC_P; split.
          by apply: qa.
       case /set2_P => // to; case: ha; ue.
       rewrite csucc_pr //; case/setI2_P => _ /setC_P [_]; case; fprops.
 -  apply: aux.
    have ->: X = X2 +s1 omga.
       set_extens t; last by case/setU1_P; [ case/setI2_P | move ->].
       move => tx; apply/setU1_P;  case: (equal_or_not t omga).
         by move ->; right.
       move => ta; left; apply/setI2_P; split => //; apply/setC_P; split.
          by apply: qa.
       case /set2_P => // to; case: hb; ue.
    rewrite csucc_pr //; case/setI2_P => _ /setC_P [_]; case; fprops.
  - left; apply: cleA => //; move: le2; rewrite - cX.
    have -> //: X2 = X.
    set_extens t; [ by move/setI2_P => [] | move => tx; apply/setI2_P]. 
    split => //; apply/setC_P; split; try apply: qa  => //.
    case/set2_P => tv; [ case: hb; ue | case: ha; ue ].
case => kk1; last first.
  have cE: cardinal E' <c n.
    apply/(cleSlt0P (CS_cardinal _) nN); rewrite  csr (csucc_pr2 aE).
    have /sub_smaller /cleSS //: sub E' (substrate r -s1 alpha).
      move => t /setC_P [tr h]; apply/setC1_P; split => // ta; case: h; ue.
  have sdr: sub (doubleton alpha omga) (substrate r) by apply: sub_set2.
  have cE2: E' =c substrate r1 by rewrite - sr1.
  move: (hrec _ cE r1 k1 cE2 or1 k1N owrk1) => [x2 [[[pa pb] pc] x2b x2c]].
  exists (x2 +s1 (doubleton alpha omga)); split => //.
  -  split; first split.
     + set_extens t.
        move/setU_P => [y ty /setU1_P]; case => yp.
         apply: sub1; rewrite - sr1 - pa; union_tac.
        by move: ty; rewrite yp; apply: sdr.
       move => tsr; case: (inc_or_not t (doubleton alpha omga)) => td.
         apply/setU_P; exists (doubleton alpha omga); fprops.
       have : inc t E' by apply/setC_P.
       rewrite - sr1 -pa => /setU_P [y ya yb]; union_tac.
    + move => a b aU bU; case/setU1_P: aU; case/setU1_P: bU => bu au.
      * exact: (pb a b au bu).
      * mdi_tac h => x xa; rewrite bu.
        have /setC_P [_  xd] //: inc x E' by  rewrite - sr1 - pa; union_tac.
      * mdi_tac h => x; rewrite au => xd xb.
        have /setC_P [_] //: inc x E' by  rewrite - sr1 - pa; union_tac.
      * by rewrite au bu; left.
    + move => t /setU1_P; case; [ by apply: pc | move ->; apply:set2_ne].
  - rewrite csucc_pr ? x2b // => dx2. 
    have /setC_P [_ /set2_P]: inc alpha E' by rewrite - sr1 - pa; union_tac.
    by case; left.
  - move => t/setU1_P []; first by move/x2c; apply:sub_total_suborders1.
    move ->; apply: (dots _ _ (proj1 ltab)).
pose Ep := Zo (substrate r) (fun z => exists2 a, inc a X1 & gle r a z).
pose Em := Zo (substrate r) (fun z => exists2 a, inc a X1 & gle r z a).
have Epmu: Ep \cup Em = substrate r.
   set_extens t; first by case/setU2_P => /Zo_S.
  move => tsr; apply/setU2_P; case: (inc_or_not t X1) => tx1.
    by left; apply: (Zo_i tsr); ex_tac; order_tac.
  have qc: sub X1 E' by ue.
  case: (p_or_not_p (forall a, inc a X1 -> ~ (gle r a t))) => hA; last first.
     left; apply: (Zo_i tsr); ex_middle bad; case: hA => a aX1 ba.
     case: bad; ex_tac.
  case: (p_or_not_p (forall a, inc a X1 -> ~ (gle r t a))) => hB; last first.
     right; apply: (Zo_i tsr); ex_middle bad; case: hB => a aX1 ba.
     case: bad; ex_tac.
  have: inc (X1 +s1 t) (free_subsets r).
    apply/free_subsetsP; split; first by apply: setU1_sub => // w /qc /sub1.
    move => a b /setU1_P aa /setU1_P bb l21; case: aa;case:bb=> aa bb.
    + by apply: Xfree.
    + by case: (hA _ bb); rewrite - aa.
    + by case: (hB _ aa); rewrite - bb.
    + by rewrite aa bb.
  by move/h2; rewrite csucc_pr // x1p - kk1 => /cleNgt; case; apply/cltS.
have  Epmi : Ep \cap Em = X1.
  set_extens t.
    move=> /setI2_P [ /Zo_P [tsr [a aX1 le2]] /Zo_P [_ [b bX1 le3]]].
    move: (Xfree a b aX1 bX1 (proj43 or _ _ _ le2 le3)) => eab.
    have <- //: a = t by rewrite - eab in le3; order_tac.
  move => tx1; move: (X1sr _ tx1); rewrite sr1 => /sub1 tE.
  by apply/setI2_P; split; apply: (Zo_i tE); ex_tac; order_tac.
have sX1Ep: sub X1 Ep  by rewrite - Epmi => t /setI2_P [].
have sX1Em: sub X1 Em  by rewrite - Epmi => t /setI2_P [].
case: (inc_or_not alpha Ep).
  move=> /Zo_P [ asr [a ax1 lear]].
  case: (equal_or_not a alpha) => eaa.
    move:(X1sr _ ax1); rewrite eaa sr1 => /setC_P [_];case; fprops.
  have naC: ~ inc a C by move/alC => le2; case: eaa; order_tac.
  set C2 := C +s1 a.   
  suff : inc C2 (total_suborders r).
    by move/ olb; rewrite (csucc_pr naC) cC => /cleNgt; case; apply/cltS.
  have C2sr: sub C2 (substrate r).
    move => t /setU1_P; case; [ apply: Csr | move ->; order_tac].
  apply:(total_suborder_prop or C2sr) => u v /setU1_P [] uc /setU1_P [] vc.
  + move: (proj2 Ctot); rewrite sioC => h; case:(h _ _ uc vc) => /iorder_gle1.
     by move => le; left.
     by move => le; right.
  + rewrite vc; right; move: (alC _ uc) => le3; order_tac.
  + rewrite uc; left; move: (alC _ vc) => le3; order_tac.
  + rewrite uc vc; left; order_tac; order_tac.
case: (inc_or_not omga Em).
  move=> /Zo_P [ asr [a ax1 lear]].
  case: (equal_or_not a omga) => eaa.
    move:(X1sr _ ax1); rewrite eaa sr1 => /setC_P [_];case; fprops.
   have naC: ~ inc a C by move/olC => le2; case: eaa; order_tac.
   set C2 := C +s1 a.   
  suff : inc C2 (total_suborders r).
    by move/ olb; rewrite (csucc_pr naC) cC => /cleNgt; case; apply/cltS.
  have C2sr: sub C2 (substrate r).
    move => t /setU1_P; case; [ apply: Csr | move ->; order_tac].
  apply:(total_suborder_prop or C2sr) => u v /setU1_P [] uc /setU1_P [] vc.
  + move: (proj2 Ctot); rewrite sioC => h; case:(h _ _ uc vc) => /iorder_gle1.
     by move => le; left.
     by move => le; right.
  + rewrite vc; left; move: (olC _ uc) => le3; order_tac.
  + rewrite uc; right; move: (olC _ vc) => le3; order_tac.
  + rewrite uc vc; left; order_tac; order_tac.
move => Ems Eps.
have subp: sub Ep (substrate r) by apply:Zo_S.
have subm: sub Em (substrate r) by apply:Zo_S.
case:(iorder_osr or subp); case(iorder_osr or subm).
set rm := induced_order _ _; set rp := induced_order _ _ => orm srm orp srp.
have eqp: Ep =c substrate rp by ue.
have eqm: Em =c substrate rm by ue.
have ltp: cardinal Ep <c n.
  apply/(cleSlt0P (CS_cardinal _) nN);rewrite - (csucc_pr Eps) csr.
  by apply: sub_smaller; apply: setU1_sub.
have ltm: cardinal Em <c n.
  apply/(cleSlt0P (CS_cardinal _) nN);rewrite - (csucc_pr Ems) csr.
  by apply: sub_smaller; apply: setU1_sub.
clear Ems Eps.
have wrpk: (order_width rp k). 
  have ha: sub X1 (substrate rp) by  rewrite  srp. 
  have fr1: inc X1(free_subsets rp).
    apply/free_subsetsP; split => //.
    by move => a b aX1 bX1 /iorder_gle1 le;apply: Xfree.
  split; first by ex_tac; rewrite x1p.
  move => T /free_subsetsP [qc qd]; apply: h2; apply/free_subsetsP.
  have Tsr: sub T (substrate r) by apply: (sub_trans qc); rewrite srp.
  rewrite srp in qc.
  split => //a b aT bT leab; apply: qd => //; apply/iorder_gleP; split; fprops.
have wrmk: (order_width rm k). 
  have ha: sub X1 (substrate rm) by  rewrite  srm. 
  have fr1: inc X1(free_subsets rm).
    apply/free_subsetsP; split => //.
    by move => a b aX1 bX1 /iorder_gle1 le;apply: Xfree.
  split; first by ex_tac; rewrite x1p.
  move => T /free_subsetsP [qc qd]; apply: h2; apply/free_subsetsP.
  have Tsr: sub T (substrate r) by apply: (sub_trans qc); rewrite srm.
  rewrite srm in qc.
  split => //a b aT bT leab; apply: qd => //; apply/iorder_gleP; split; fprops.
case: (hrec _ ltp _ _  eqp orp kN wrpk).
case: (hrec _ ltm _ _  eqm orm kN wrmk).
rewrite srm srp => Pm [Pma Pmb Pmc] Pp [Ppa Ppb Ppc].
pose FP x := select (fun z => inc x z).
have HFP E P: partition_s P E -> 
  forall x, inc x E -> inc x (FP x P) /\ inc (FP x P) P.
  move => [[qa qb] qc] x xE; apply: select_pr.
     rewrite - qa in xE; move /setU_P: xE=> [y ya yb]; ex_tac.
  move => a b /= aY xa bY xb; case: (qb a b aY bY) => // dab; empty_tac1 x.
pose fp x:= select (fun z => inc x z) Pp.
have Hap x: inc x Ep -> inc x (fp x) /\ inc (fp x) Pp by apply: HFP.
pose fm x:= select (fun z => inc x z) Pm.
have Ham x: inc x Em -> inc x (fm x) /\ inc (fm x) Pm by apply: HFP.
have injfp: {inc X1 &, injective fp}.
  move => x y xX1 yX1 /=; move: (Hap _ (sX1Ep _ xX1)) (Hap _ (sX1Ep _ yX1)).
  move => [pa pb] [pc pd] pe; rewrite - pe in pc.
  move:(Ppc _ pb) => /total_subordersP [qa qb].
  move: (proj2 qb x y); rewrite iorder_sr // => h; move: (h pa pc). 
  case=>/iorder_gle1 /iorder_gle1 => le.
    by apply:(Xfree _ _ xX1 yX1).
  by symmetry;apply:(Xfree _ _ yX1 xX1). 
have injfm: {inc X1 &, injective fm}.
  move => x y xX1 yX1 /=; move: (Ham _ (sX1Em _ xX1)) (Ham _ (sX1Em _ yX1)).
  move => [pa pb] [pc pd] pe; rewrite - pe in pc.
  move:(Pmc _ pb) => /total_subordersP [qa qb].
  move: (proj2 qb x y);rewrite iorder_sr // => h; move: (h pa pc). 
  case=>/iorder_gle1 /iorder_gle1 => le.
    by apply:(Xfree _ _ xX1 yX1). 
  by symmetry;apply:(Xfree _ _ yX1 xX1). 
have cX1: cardinal X1 = k by ue.
have fsX1: finite_set X1 by apply /NatP; ue.
have axp: lf_axiom fp X1 Pp by move => x /sX1Ep /Hap[].
have axm: lf_axiom fm X1 Pm by move => x /sX1Em /Ham[].
have bijfp: bijection (Lf fp X1 Pp).
  by apply:bijective_if_same_finite_c_inj; aw; trivial;try ue; apply: lf_injective.
have bijfm: bijection (Lf fm X1 Pm).
  by apply:bijective_if_same_finite_c_inj; aw; trivial;try ue; apply: lf_injective.
pose fpm x := fp x \cup fm x.
have ra: union (fun_image X1 fpm) = substrate r.
  set_extens t.
    move/setU_P => [y ty /funI_P [z zx1 yv]].
    move: ty; rewrite yv => /setU2_P [].
      move: (Hap _ (sX1Ep _ zx1)) => [za zb] tp; apply: subp.
      rewrite - (proj1 (proj1 Ppa)); union_tac.
    move: (Ham _ (sX1Em _ zx1)) => [za zb] tp; apply: subm.
    rewrite - (proj1 (proj1 Pma)); union_tac.
  rewrite - Epmu => /setU2_P; case.
    rewrite - (proj1 (proj1 Ppa)) => /setU_P [y ty yp].
    move: (proj2 (proj2 bijfp) y); aw => h; move:(h yp) => [x xX1]; rewrite LfV// => yv.
    by apply/setU_P; exists (fpm x); [ apply/setU2_P; left; ue | apply:funI_i].
  rewrite - (proj1 (proj1 Pma)) => /setU_P [y ty yp].
  move: (proj2 (proj2 bijfm) y); aw => h; move:(h yp) => [x xX1]; rewrite LfV// => yv.
  by apply/setU_P; exists (fpm x); [ apply/setU2_P; right; ue | apply:funI_i].
have aux i j x: inc i X1 -> inc j X1 ->  inc x (fp i) -> inc x (fm j)->  i= j.
      move => ix jx xxi xxj.
      move: (Hap _ (sX1Ep _ ix)) (Ham _ (sX1Em _ jx)) => [qa qb][qc qd].
move: Ppa Pma => [[sa sb] _] [[sc sd] _].
  have xp: inc x Ep by  rewrite - sa; union_tac.
  have xm: inc x Em by  rewrite - sc; union_tac.
  have xx1: inc x X1 by rewrite - Epmi; fprops.
  have -> : i = x.
    move: (Ppc _ qb) => /total_subordersP [qe [qf]].
    rewrite (iorder_sr orp qe) => tt; move: (tt i x qa xxi).
    case; move/iorder_gle1/iorder_gle1=> cp.
       exact:(Xfree i x ix xx1 cp).
    by rewrite (Xfree x i xx1 ix cp).
  have -> // : j = x.
  move: (Pmc _ qd) => /total_subordersP [qe [qf]].
  rewrite (iorder_sr orm qe) => tt; move: (tt j x qc xxj).
  case; move/iorder_gle1/iorder_gle1=> cp.
    exact:(Xfree j x jx xx1 cp).
  by rewrite (Xfree x j xx1 jx cp).
have aux2 x i j: inc i X1 -> inc j X1 ->inc x (fpm i) -> inc x (fpm j) -> i = j.
  move: Ppa Pma => [[sa sb] _] [[sc sd] _] ix jx.
  case/setU2_P => xx; case/setU2_P => yy.
    + move: (Hap _ (sX1Ep _ ix)) (Hap _ (sX1Ep _ jx)) => [qa qb][qc qd].
      move: (sb _ _ qb qd); case => sf; last by empty_tac1 x.
      by move:(injfp _ _ ix jx sf) => ->. 
    + by rewrite (aux _ _ _ ix jx xx yy).
    + by rewrite (aux _ _ _ jx ix yy xx).
    + move: (Ham _ (sX1Em _ ix)) (Ham _ (sX1Em _ jx)) => [qa qb][qc qd].
      move: (sd _ _ qb qd); case => sf; last by empty_tac1 x.
      by rewrite(injfm _ _ ix jx sf).
have rb: partition_s (fun_image X1 fpm) (substrate r).
  split; first split => //. 
    move => a b /funI_P[i ix ->] /funI_P[j jx ->]; mdi_tac hh => x x1 x2.
    by case: hh; rewrite (aux2 x i j ix jx x1 x2).
  move => t /funI_P [z zX1 ->]; move:  (proj1(Hap _ (sX1Ep _ zX1))) => zi.
  by exists z; apply/setU2_P; left.
have rc: cardinal (fun_image X1 fpm) = k.
  rewrite cardinal_fun_image // => i j ix jx hh.
  move: (proj1 (Hap _ (sX1Ep _ ix))) => qa.
  have qb: inc i (fpm i) by apply/setU2_P; left.  
  have qc: inc i (fpm j) by ue.
  exact:(aux2 i i j ix jx qb qc).
exists (fun_image X1 fpm); split => // t /funI_P [x x1 ->].
move:  (Hap _ (sX1Ep _ x1)) (Ham _ (sX1Em _ x1)) => [qa qb][qc qd].
move: Ppa Pma => [[sa sb] _] [[sc sd] _].
have s1: sub (fpm x) (substrate r).
  move => y /setU2_P [] yy; first by  apply: subp; rewrite - sa; union_tac.
   apply: subm; rewrite - sc; union_tac.
have hp a b: inc a (fp x) -> inc b (fp x) -> ocomparable r a b.
  move/total_subordersP: (Ppc _ qb) => [pa [pb]].
  rewrite (iorder_sr orp pa) => hp af bf.
  by case: (hp a b af bf) => /iorder_gle1/iorder_gle1; [left | right].
have hm a b: inc a (fm x) -> inc b (fm x) -> ocomparable r a b.
  move/total_subordersP: (Pmc _ qd) => [pa [pb]].
  rewrite (iorder_sr orm pa) => hm af bf.
  by case: (hm a b af bf) => /iorder_gle1/iorder_gle1; [left | right].
have hap a: inc a (fp x) -> gle r x a.
  move => afp.
  have: inc a Ep by rewrite - sa; union_tac.
  move=> /Zo_P [asr [b bX1 le2]]; case:(hp x a qa afp) => // lax.
  by rewrite - (Xfree _ _ bX1 x1 (proj43 or _ _ _ le2 lax)).
have ham a: inc a (fm x) -> gle r a x.
  move => afp.
  have: inc a Em by rewrite - sc; union_tac.
  move=> /Zo_P [asr [b bX1 le2]]; case:(hm x a qc afp) => // lax.
  by rewrite (Xfree _ _ x1 bX1 (proj43 or _ _ _ lax le2)).
apply:(total_suborder_prop or s1) => a b;case/setU2_P => xx; case/setU2_P => yy.
+ by apply: hp.
+ right; move: (hap _ xx)  (ham _ yy) => la lb; order_tac.
+ left; move: (ham _ xx)  (hap _ yy) => la lb; order_tac.
+ by apply: hm.
Qed.


(* old 
Lemma Exercise4_5a Y T k:
  cardinal Y = k -> cardinal T = k -> natp k ->
  sub T (union Y) -> disjoint_ser T ->
  (forall Z, inc Z Y -> small_set (T \cap Z)) ->
  (forall Z, inc Z Y -> singletonp (T \cap Z)).
Proof.
move => cY cT kN Tu ald als.
set V1 := Zo Y (fun z => (T \cap z) <> emptyset).
set V2 := Lg V1 (fun z => (T \cap z)). 
move=> Z ZY; case: (small_set_pr (als _ ZY)) => // itz.
have s1: sub V1 Y by apply: Zo_S.
have fsy: finite_set Y by apply /NatP; rewrite cY.
have xy: V1 <> Y.
  by move=> TZ; move: ZY;rewrite -TZ; move /Zo_P => [_].
move: (strict_sub_smaller (conj s1 xy) fsy) => [_ bad] {itz s1 xy fsy ZY}.
case: bad.
have v1p: forall x, inc x V1 -> cardinal (Vg V2 x) = \1c.
  move=> x xV1; rewrite /V2; bw.
  move: xV1 => /Zo_P [zY ine].
  by case: (small_set_pr (als _ zY)) => // [] [y] ->; rewrite cardinal_set1.
move: (csum_of_ones V1); rewrite /csum /disjointU.
set duf:= disjointU_fam _ ;set D:= unionb _ => <-.
rewrite cY - cT.
have pa: fgraph duf by rewrite /duf/disjointU_fam;  fprops.
have pb:fgraph V2 by rewrite /V2; fprops.
have pc: domain duf = domain V2 .
  rewrite  /duf/disjointU_fam/V2/cst_graph; bw.
have pd: (forall i, inc i (domain duf) -> (Vg duf i) =c (Vg V2 i)).
  rewrite  /duf/disjointU_fam/V2/cst_graph; bw.
  move=> i iV1; bw.
  rewrite (card_card CS1) -(v1p _ iV1) /V2; bw.
have pe:  mutually_disjoint duf. 
  apply: disjointU_disjoint; rewrite /cst_graph; fprops.
have pf: mutually_disjoint V2.
  rewrite /V2; apply: mutually_disjoint_prop2. 
  move=> i j y => /Zo_S iY /Zo_S jY /setI2_P [_ yi] /setI2_P [_ yj].
  case: (ald _ _ iY jY) => // di; empty_tac1 y.
move: (Eq_disjointU (conj pc pd) pe pf). 
have -> //: unionb V2 = T.
rewrite /V2;set_extens t.
  by move /setUb_P; bw; move =>  [y yv1]; bw; move /setI2_P => [].
move=> tT; move: (Tu _ tT) => /setU_P  [y ty yY].
have tv: inc t (T \cap y) by apply: setI2_i.
have nei: nonempty (T \cap y) by exists t.
have yv1: inc y V1 by apply: Zo_i => //; apply /nonemptyP.
apply/setUb_P;exists y; bw.
Qed.
 *)


(** Proof by induction on the cardinal of [E], when it is finite. *)

Lemma Exercise4_5b r k: finite_set (substrate r) ->
  order r -> natp k ->  order_width r k -> Exercise4_5_conc r k.
Proof.
move /NatP; set n := cardinal (substrate r).
move: (refl_equal n); rewrite {2} /n.
move: n; move=> n nc nN; move: n nN r k nc; apply: Nat_induction1.
move=> n nN hrec r k csr or kN [[X Xf cX] h2].
(** The case where [E] is empty is trivial *)
case: (emptyset_dichot (substrate r)) => sre.
  move: Xf =>  /Zo_P []; rewrite /Exercise4_5_conc sre; move /setP_P => Xse _.
  exists emptyset => //;split. 
  + split;last by move=> a /in_set0.
    by split => //; try split => //; [rewrite setU_0 |move=> a b /in_set0].
  + by move/sub_set0: Xse => <-.
  + by move=> x /in_set0.
(** Assumption: we have a free set [X] with [k] elements, all other free
subsets have at most [k] elements. We have chosen an element [a], the 
complementary is [E'].  The results holds, for any [k], on sets with less
than [n] elements. In particular, if no free subset of [E'] has [k] elements,
we can partition [E'] in [k-1] subsets, and add [(singleton a)] as last set.  *)
have fse: finite_set (substrate r) by hnf;rewrite - csr; apply /NatP; fprops.
move: (finite_set_minimal or fse sre) => [a [asr amin]].
move: (csucc_pr1 (substrate r) a).
rewrite (setC1_K asr) - csr; set E':= _ -s1 _ => eq1.
set r' := induced_order r E'.
have sE': sub E' (substrate r) by apply: sub_setC.
move: (iorder_osr or sE')=> [or' sr'].
set p1:=  (cardinal E').
have p1c: p1 = (cardinal (substrate r')) by ue.
have p1N: natp p1 by apply: (NS_nsucc (CS_cardinal E')); ue.
move: (cltS p1N); rewrite - eq1 => p1n.
have fsE T:  inc T (free_subsets r') -> inc T (free_subsets r).
  move=> /free_subsetsP [p3 p2]; apply/free_subsetsP; split.
    by apply: (sub_trans _ sE'); ue.
  move => x y xt yt lexy;apply: p2=> //. 
  by apply /iorder_gle0P => //;rewrite - sr'; apply: p3.
have h21 x: inc x (free_subsets r') -> (cardinal x) <=c k.
  by move/fsE; apply: h2.
rewrite - sr' in sE'.
case: (p_or_not_p (exists2 X', 
   inc X' (free_subsets r') & cardinal X' = k)); last first.
  move=> ne.
  set X1 := X -s1 a.
  have X1f: inc X1 (free_subsets r'). 
    move/free_subsetsP: Xf => [p3 p2]; apply/free_subsetsP; split.
      by rewrite sr' => t /setC1_P [/p3 tX ta]; apply /setC1_P. 
    move=> u v  => /setC1_P [uX _] /setC1_P [vX _] uv.
    by move: (iorder_gle1 uv);apply: p2.
  case: (inc_or_not a X) => aX; last first.
    by case: ne; exists X => //; rewrite - (setC1_eq aX).
  move: (csucc_pr1 X a); rewrite setC1_K // -/X1 cX.
  set k1:= (cardinal X1) => ks.
  have kN': natp k1 by apply: NS_nsucc; rewrite /k1; fprops; ue.
  have krec: order_width r' k1.
    split; first by exists X1.
    move=> x xsr'; move: (h21 _ xsr') => le1.
    have: (cardinal x) <c k by split => //  xk; case: ne; ex_tac.
    by rewrite ks; move /(cltSleP kN').
  move: (hrec p1 p1n _ _ p1c or' kN' krec)  => [Y [[[uY adi] ane] cY altY]].
  have nauy: ~(inc a (union Y)).
     by rewrite uY sr' /E'; move /setC1_P => [_]. 
  have nsY: ~ inc (singleton a) Y.
    move=> say; case: nauy; apply: (@setU_i _ (singleton a)); fprops.
  move: (csucc_pr nsY); rewrite cY -ks => p3.
  set Y' := (Y +s1 (singleton a)).
  have pr1: union Y' = substrate r.
    set_extens t.
      move=>  /setU_P [y ty];case /setU1_P => tY.
        apply: sE'; rewrite  -uY; union_tac.
      by move: ty; rewrite tY; move /set1_P => ->.
    move=> tsr; case: (equal_or_not t a) => ta.
      rewrite /Y' - ta;apply /setU_P; exists (singleton t);fprops.
    have: inc t (substrate r') by rewrite sr'; apply /setC1_P; fprops.
    rewrite /Y' -uY => /setU_P [y ty uyY]; union_tac.
  have pr2: disjoint_set Y'.
    move => u v; case /setU1_P => us; case /setU1_P => vs.
    +  by apply: adi.
    + right; rewrite vs; apply: disjoint_pr => t tu /set1_P ta.
      case: nauy; rewrite -ta; union_tac.
    + right; rewrite us; apply: disjoint_pr => t /set1_P ta tu.
      case: nauy; rewrite -ta; union_tac.
    + by left;rewrite us vs.  
  have pr3: alls Y' nonempty.
   move=> u; case /setU1_P; [ by apply: ane| move=> ->; apply: set1_ne].
  exists (Y +s1 (singleton a)); split => //.
  move => x; case /setU1_P => xy.
    move /total_subordersP: (altY _ xy) => [sx []];rewrite iorder_sr // => orx torx.
    have sx1: sub x (substrate r).
      by apply: (@sub_trans (substrate r')) => //; rewrite sr' //.
    apply /total_subordersP; split; first exact.
    move: (iorder_osr or sx1) => [pa pb].
    split => //; rewrite pb=> y z yx zx; case: (torx _ _ yx zx) => le1.
    - by left; apply /iorder_gleP => //;move: (iorder_gle1(iorder_gle1 le1)).
    - by right; apply /iorder_gleP => //;move: (iorder_gle1(iorder_gle1 le1)).
   have xsr: sub x (substrate r) by rewrite xy; apply: set1_sub.
   move: (iorder_osr or xsr) => [pa pb].
   apply/total_subordersP; split =>//;split => //; rewrite pb xy;move=> y z. 
   by move =>/set1_P -> /set1_P ->; left; apply /iorder_gle0P; fprops; order_tac.
(** We assume now that there is a free subset with [k] elements in [E']
   and partition [E'] into [k] parts. Let [f T] be the set of elements of [T] 
   that are [>= a]. Assume that there is [Z] in the partition 
   such that any free subset that contains no element of [f Z] has less
   than [k] elements. By induction we partition the complement of [f Z] 
   into [k-1] sets, and add [f Z] as last set.
 *)
move=> h22.
have krec: order_width r' k by [].
move: (hrec p1 p1n _ _ p1c or' kN krec)=> [Y [[[uY adi] ane] cY altY]].
pose f T := Zo T (fun z => gle r a z).
case: (p_or_not_p (exists2 Z, inc Z Y &
   forall T, inc T (free_subsets (induced_order r (E' -s  (f Z))))
     -> (cardinal T) <c k)).
  move => [Z ZY hZ].
  set E'':= (E' -s (f Z)).
  set r'':= induced_order r E''.
  have sEs: sub E'' (substrate r). 
    apply: (@sub_trans E') => //; apply: sub_setC.
  move: (iorder_osr or sEs) => [or'' sr''].
  set X1:= X \cap (E' -s  (f Z)).
  have X1f: inc X1 (free_subsets r'').
    apply/free_subsetsP;split; first by  rewrite sr'';apply: subsetI2r. 
    move=> x y /setI2_P [xX _] /setI2_P [yX _] le1.
    move: Xf => /Zo_P [p3 p2].
    exact: (p2 x y xX yX (iorder_gle1 le1)).
  move: (hZ _ X1f) => le1.
  have knz: k <> \0c by move=> kz; rewrite kz in le1; case: (clt0 le1).
  move: (cpred_pr kN knz); set k1 := cpred k; move => [k1N k1s].
  have krec1: order_width r'' k1.
    split; last by move=> x xr; move: (hZ _ xr);rewrite k1s; move/(cltSleP k1N).
    move: Xf => /Zo_P [] /setP_P aa bb.
    have cXp: forall x, inc x (X -s X1) ->
      (inc x X /\ (x = a \/ (inc x Z  /\ gle r a x))).
      move=> x /setC_P [xX] /setI2_P => x1.
      split => //; case: (equal_or_not x a) => xa;first by left.
      right; ex_middle aux; case: x1; split => //;  apply /setC_P;split => //.
        by apply /setC1_P;split => //; apply: aa.
      by apply /Zo_P.
    have sc: small_set (X -s X1). 
      move=> x y xc yc; move: (cXp _ xc) (cXp _ yc) => [xX ex] [yX ey].
      case: ex => xp; case: ey => yp.
      + by rewrite xp yp.
      + by move: yp; rewrite -xp; move => [_ xy]; apply: bb.
      + by symmetry;move: xp; rewrite -yp; move => [_ xy]; apply: bb.
      + move: xp yp => [xz _] [yz _].
        move /total_subordersP: (altY _ ZY) => [Zs [orz]]; rewrite iorder_sr// => aux.
        by case: (aux _ _ xz yz) => le2;[ | symmetry];
          move: (iorder_gle1 (iorder_gle1 le2)) => le3; apply:bb.
    have X1c: sub X1 X by apply: subsetI2l.
    move: (cardinal_setC X1c); rewrite cX k1s.
    have cX1: cardinalp (cardinal X1) by fprops.
    case: (small_set_pr sc) => cp1.
      rewrite /cdiff cp1 cardinal_set0 csum0r //. 
      move=> le2; case: (proj2 le1); ue.
    rewrite /cdiff; move: cp1; move=> [x] ->.
    rewrite cardinal_set1 - csucc_pr4 // => ssc.
    by exists X1 => //; apply: csucc_inj; fprops.
  set p2 := cardinal (E' -s (f Z)).
  have p2c: p2 = cardinal (substrate r'') by ue.
  have ee'': sub E'' E' by apply:  sub_setC.
  move: (sub_smaller  ee''); rewrite -/p1 -/p2 => p12.
  have p2n:= cle_ltT p12 p1n.
  move: (hrec p2 p2n _ _ p2c or'' k1N krec1)
    => [Y' [[[uY' adi'] ane'] cY' altY']].
  set U1 := (f Z) +s1 a.
  have nauy: ~(inc a (union Y')).
     by rewrite uY' sr''; move /setC_P => [] /setC1_P [_].
  have nsY: ~ inc U1 Y'.
    move=> say; case: nauy; apply: (@setU_i _ U1);  rewrite /U1;fprops.
  move: (csucc_pr nsY); rewrite cY' -k1s => p3.
  have Zr': sub Z (substrate r') by rewrite -uY; apply: setU_s1.
  have Zr: sub Z (substrate r) by apply: (@sub_trans  (substrate r')).
  have U1r: sub U1 (substrate r).
    move=> t;case /setU1_P ; last by move => ->.
    by move /Zo_P => [tz _]; apply: Zr.
  set Y'' := Y' +s1 U1.
  have pr1:union Y'' = substrate r.
    set_extens t.
      move=> /setU_P [y ty /setU1_P[]] tY.
        apply: sEs; rewrite - sr'' -uY'; union_tac.
      move: ty; rewrite tY;apply: U1r.
    move=> tsr; apply /setU_P;case: (equal_or_not t a) => ta.
      rewrite ta/Y'';exists U1 => //; rewrite /U1;fprops.
    have tE': inc t E' by  apply /setC1_P; split.
    case: (inc_or_not t (f Z)) => tf.
      exists U1 => //; rewrite /Y''/U1;fprops.
    have : inc t E'' by apply /setC_P; split.
    rewrite - sr'' -uY'/Y'';move=> /setU_P [y ty yy]; exists y; fprops.
  have aux: forall u,inc u Y' -> disjoint u U1.
      move => u uy; rewrite /U1;apply: disjoint_pr => t tu /setU1_P ta.
      have : inc t (union Y') by union_tac.
      case: ta; last by move => ->; apply: nauy.
      by rewrite uY' sr'' => tf; move /setC_P => [_]; case.
  have pr2:disjoint_set Y''.
    move => u v;case /setU1_P => us; case /setU1_P => vs.
    + by apply: adi'.
    + by right; rewrite vs; apply: aux.
    + by right; apply /disjoint_S;rewrite us; apply: aux.
    + by left;rewrite us vs.
  have pr3: alls Y'' nonempty.
    move=> u; case /setU1_P; [ by apply: ane'| move=> ->; exists a]. 
    rewrite /U1;fprops.
  exists Y''; split => //.
  move => x;case /setU1_P => xy.
    move /total_subordersP: (altY' _ xy) => [sx []]; rewrite iorder_sr// => orx torx.
    have sx1: sub x (substrate r).
      by apply: (@sub_trans  (substrate r'')) => //; rewrite sr'';apply: sEs. 
    move: (iorder_osr or sx1) => [pa pb].
    apply/total_subordersP; split => //.
    split => //; rewrite pb=> y z yx zx; case: (torx _ _ yx zx) => le2.
      by left; apply /iorder_gleP => //; move: (iorder_gle1 (iorder_gle1 le2)).
    by right;apply /iorder_gleP => //; move: (iorder_gle1(iorder_gle1 le2)).
  rewrite xy; apply:(total_suborder_prop or U1r) => x1 y1 x1u y1u.
  move/total_subordersP: (altY _ ZY)=> [_ [_]]; rewrite iorder_sr//; move=> torz.  
  move: x1u y1u; case /setU1_P=> x1p; case /setU1_P => y1p.
  + move: x1p y1p => /Zo_S a1 /Zo_S a2.
    by case:(torz _ _ a1 a2) => /iorder_gle1 /iorder_gle1 h; [left | right].
  + by rewrite y1p; move: x1p => /Zo_hi; right.
  + by rewrite x1p; move: y1p => /Zo_hi; left.
  + by rewrite x1p y1p; left; order_tac.
(** For each [Z] in the partition [Y],
 there is [g Z] a free subset with [k] elements in the complement of [f Z] *)
pose io Z := (induced_order r (E' -s (f Z))).
move=> bad.
have Zp1:  forall Z,  sub (E' -s (f Z)) (substrate r).
  move=> Z ;by apply: (@sub_trans E'); [ apply: sub_setC | ue].
have Zp2:  forall Z, substrate (io Z) = E' -s (f Z).
   move => Z;rewrite /io iorder_sr//.
have sfr:  forall Z T, inc Z Y ->
  inc T (free_subsets (io Z)) ->  inc T (free_subsets r).
  move=> Z T ZY  /Zo_P [] /setP_P pa pb; apply /Zo_P.
  move: (Zp1 Z)(Zp2 Z) => pc pd; rewrite pd in pa.
  split; first by apply /setP_P;apply: (@sub_trans (E' -s (f Z))).
  by move=> x y xT yT xy; apply: pb => //; apply /iorder_gle0P => //; apply: pa.
have good: forall Z, inc Z Y -> exists2 T, 
     inc T (free_subsets (io Z)) & cardinal T = k.
  move => Z ZY; ex_middle bad2.
  case: bad; exists Z => // T Tf.
  move: (sfr _ _ ZY Tf) => f1.
  split; first by apply: (h2 _ f1).
  case: (equal_or_not (cardinal T) k) => // Tk; case: bad2; ex_tac.  
pose g Z := choose(fun T => inc T (free_subsets(io Z)) /\ cardinal T = k).
have gp1: forall Z, inc Z Y ->
  (inc (g Z) (free_subsets (io Z)) /\ cardinal (g Z) = k).
  by move=> Z /good [t ta tb]; apply choose_pr; exists t.
clear bad good.
(** Let [W] the set of all free subsets of [E']  that have [k] elements.
Then  [g Z] is in [W]. An element of [W] intersects [Z] at most once.
By the previous lemma, the intersection of [g Z] and [T] is a singleton
say [sij Z T], whenever [Z] and [T] are in the partition.
The relations [(sij Z T) <= a] are false; as well as [a <= (sij Z Z)].
 *)

pose krec1 T:= [/\ inc T (free_subsets r), sub T E' & cardinal T = k].
have gp2: forall Z, inc Z Y -> krec1 (g Z).
  move=> Z ZY; move: (gp1 _ ZY) => [pa pb]; split => //.
    apply: (sfr _ _ ZY pa).
  move: pa =>/Zo_P [] /setP_P pa _.
  apply: (sub_trans pa); rewrite /io iorder_sr //; apply: sub_setC.
have gp3: forall T Z,  krec1 T -> inc Z Y -> small_set (T \cap Z).
  move=> T Z [pa pb pc] ZY x y /setI2_P [xT xZ] /setI2_P [yT yZ].
  move: pa => /Zo_P [_ aux2].
  move /total_subordersP: (altY _ ZY) => [Zr'[_]]; rewrite iorder_sr//;move=> tor. 
  have Zr: sub Z (substrate r) by apply: (@sub_trans  (substrate r')).
  case: (tor _ _ xZ yZ)=> aux.
    by move: (iorder_gle1 (iorder_gle1 aux)); apply: aux2.
    by symmetry; move: (iorder_gle1 (iorder_gle1 aux)); apply: aux2.
have gp4: forall T Z,  krec1 T -> inc Z Y ->
    singletonp (T \cap Z).
  move => T Z kr; move: (kr) => [kt1 kt2 kt3]. 
  have stu: sub T (union Y) by rewrite uY  sr'.
  apply: (Exercise4_5a cY kt3 kN stu adi). 
  move=> z zy;apply: (gp3 _ _ kr zy).
pose sij z1 z2 := union ((g z1) \cap z2).
have sijp: forall z1 z2, inc z1 Y -> inc z2 Y ->
   (g z1) \cap z2 = singleton (sij z1 z2).
  move=> z1 z2 z1Y z2Y; rewrite /sij; move: (gp4 _ _ (gp2 _ z1Y) z2Y) => [s] ->.
  by rewrite setU_1.
have sij1: forall i j, inc i Y -> inc j Y -> inc (sij i j) (g i).
   move => i j iY jY; apply: (@setI2_1 _ j). 
   rewrite (sijp _ _ iY jY); fprops.
have sij2: forall i j, inc i Y -> inc j Y -> inc (sij i j) j.
   move => i j iY jY; apply: (@setI2_2 (g i)).
   rewrite (sijp _ _ iY jY); fprops.
have sija1: forall i j, inc i Y -> inc j Y -> gle r  (sij i j) a-> False.
  move=> i j iY jY; move: (sij1 _ _ iY jY) => aux2.
  move: (gp1 _ iY) => [] /Zo_P [] /setP_P; rewrite /io iorder_sr // => s1 _.
  move: (s1 _ aux2) => /setC_P [] /Zo_P [pa] /set1_P pb pc _.
  by move => aux1; move: (amin _ aux1).
have sija2: forall i, inc i Y-> gle r a (sij i i) -> False.
  move=> i iY; move: (sij1 _ _ iY iY) => pa pc.
  move: (gp1 _ iY) => [] /Zo_P [] /setP_P; rewrite /io iorder_sr // => s1 _.
  move: (s1 _ pa) => /setC_P [] /Zo_P [pb] /set1_P pe pd _. 
  by case: pd; apply: Zo_i=> //; apply: sij2.

(** Fix [T]; consider the least of the [sij Z T]. This exists, since we 
consider a non-empty finite subset of a totally ordered set.
This gives some [sj T]. These elements are all distinct.
Together with [a], we get a free subset with [k+1] elements, absurd.  *)
pose V1 j:= fun_image Y (fun i => sij i j).
pose sj j := the_least (induced_order r (V1 j)).
have v1p: forall j, inc j Y ->
   let r1 := (induced_order r (V1 j)) in
     [/\ order r1, substrate r1 = V1 j & least r1 (sj j)].
  move=> j jY r1.
  have s1: sub (V1 j) j. 
    move => t /funI_P [z zY ->]; apply: (sij2 _ _ zY jY).
  have s0: sub j (substrate r') by move=> t tj;rewrite -uY; union_tac.
  have s2:= (sub_trans s1 s0).
  have s3:= (sub_trans s2 sE').
  have s4:= (sub_trans s0 sE').
  move: (iorder_osr or s3) => [or1 pb].
  have ne1:  nonempty (V1 j) by exists (sij j j); apply /funI_P; ex_tac.
  have fs1: finite_set (V1 j) by apply: ( sub_finite_set s3 fse).
  rewrite /r1;saw; apply: the_least_pr => //.
  have s5: sub (V1 j) (substrate (induced_order r j)) by rewrite iorder_sr.
  move/total_subordersP:(altY _ jY) => [_ tor1].
  rewrite - (iorder_trans r s1).
  apply: finite_subset_torder_least => //.
  rewrite - (iorder_trans r s0)  sr'//.
have v2p: forall i j, inc i Y -> inc j Y ->
   gle r (sj i) (sj j) -> i = j. 
  move=> i j iY jY leij. 
  move: (v1p _ iY) (v1p _ jY) => [o1 sr1 le1][o2 sr2 le2].
  move: le1 => []; rewrite sr1; move /funI_P => [z zY sa] _.
  have sb: inc (sij z j) (substrate (induced_order r (V1 j))).
    rewrite sr2; apply /funI_P; ex_tac.
  move:le2  => [le3 le4]; move: (le4 _ sb) => le5.
  move: (order_transitivity or leij (iorder_gle1 le5)); rewrite  sa => le6.
  move: (sijp _ _ zY iY)(sijp _ _ zY jY) => s1 s2.
  move: (gp2 _ zY) => [fk _]; move: fk => /Zo_P [_ fk2].
  move: (fk2 _ _ (sij1 _ _ zY iY) (sij1 _ _ zY jY) le6).
  move: (sij2 _ _ zY iY) (sij2 _ _ zY jY) => i1 i2 sv.
  case: (adi _ _ iY jY) => //; rewrite /disjoint => di.
  empty_tac1 (sij z i); apply: setI2_i => //; ue.
set V2 := fun_image Y sj.
have sii: forall j, inc j Y-> exists2 i, inc i Y & sj j = sij i j.
  move=> j jY; move: (v1p _ jY) => [pa pb [pc pd]].
  move:pc; rewrite pb => /funI_P [z zY ->]; ex_tac.
have v3p: forall j, inc j Y -> inc (sj j) (substrate r).
  move=> l lY;move: (sii _ lY) => [j jY ->].
  apply: sE'; rewrite -uY; move: (sij2 _ _ jY lY) => su; union_tac.
have c2: cardinal V2 = k.
   symmetry; rewrite - cY; apply /card_eqP.
   exists (Lf sj Y V2); hnf; rewrite lf_source lf_target; split => //.
   apply: lf_bijective.
      move=> t TY; apply /funI_P; ex_tac.
    move=> u v uY1 vY ss; apply: (v2p _ _ uY1 vY); rewrite - ss; order_tac.
    by apply: v3p.
  by move => y /funI_P.
set v3:= V2 +s1 a.
have an2: ~ (inc a V2).
  move=> /funI_P [z zY]; move: (sii _ zY) => [j jY] -> ta.
  by case: (sija1 _ _ jY zY); rewrite - ta; order_tac.
move: (csucc_pr an2); rewrite c2;set (V3:= V2 +s1 a) => bad1.
have V3t: inc V3 (free_subsets r).
  apply: Zo_i. 
    apply /setP_P => t; case /setU1_P; last by move => ->. 
    by move=> /funI_P [z zY ->];apply: v3p.
  move=> x y ; case /setU1_P => pa; case /setU1_P => pb.
  + move: pa pb => /funI_P [z zY ->] /funI_P [z' zY' ->]. 
    by move=> aux; rewrite (v2p  _ _ zY zY' aux).
  + rewrite pb; move: pa => /funI_P [z zY ->].
    move: (sii _ zY) => [j jY ->] le1.
    case: (sija1 _ _ jY zY le1).
  + rewrite pa; move: pb => /funI_P [z zY ->].
    move: (v1p _ zY) => [qa qb [qc qd]] asj; rewrite qb in qd.
    have sb: inc (sij z z) (V1 z) by apply /funI_P; ex_tac.
    move: (order_transitivity or asj (iorder_gle1 (qd _ sb))) => le2.
    case: (sija2 _ zY le2).
  + by rewrite pa pb.
move: (h2 _ V3t); rewrite bad1 => pa; case: (cleNgt pa (cltS kN)).
Qed.


(** Proof by induction on [k] in the general case; [k=0] is trivial *)

Lemma Exercise4_5d r k:
  order r -> natp k -> order_width r k -> Exercise4_5_conc r k.
Proof.
move=> or kN; move: k kN r or.
apply:Nat_induction.
  move=> r or [hyp1 hyp2]; exists emptyset.
  case: (emptyset_dichot (substrate r)).
     move => ->; rewrite cardinal_set0; split => //. 
     split; last by move=> a /in_set0.
     split; first by apply: setU_0. 
     by move=> a b /in_set0.
    by move=> x /in_set0.
  move=> [x sxr].
  have px: inc (singleton x) (free_subsets r).
    apply: Zo_i; first by apply /setP_P; apply: set1_sub.
    by move=> u v  /set1_P -> /set1_P ->.
  move:(hyp2 _ px); rewrite cardinal_set1 => h.
  by move: (cle0 h) => h1; case: card1_nz.
move=> k kN hrec r or [[X0 X0f cX0] gensiz].
(** We assume the result true for [k], and [X0] is free with [k+1] elements.
Assume that there is a totally ordered set [C], such that any free subset in
the complementary has at most [k] elements. Then there is a free subset with [k]
elements, we can partition the complement into [k] subsets. With [C], this 
gives [k+1] sets.
 *)
pose comp C := ((substrate r) -s C).
pose indC C := induced_order r ((substrate r) -s C).
suff: exists2 C, inc C (total_suborders r) &
    (forall T, sub T (comp C) ->  (free_subset r T) ->(cardinal T) <=c k).
  move=> [C /total_subordersP [Cs torC ]h1].
  set E1 := comp C.
  have s1: sub E1 (substrate r) by apply: sub_setC.
  set r1:= indC C.
  move: (iorder_osr or s1) => [or1 sr1].
  have p1: forall x, inc x (free_subsets r1) -> (cardinal x) <=c k.
    move => x /free_subsetsP[p1 p2].
    have p3: free_subset r x.
     move=> u v ux vx uv; apply:p2 =>//;rewrite /r1 /indC -/(comp C) -/E1 - sr1.
     by apply /iorder_gle0P => //; apply: p1.
    rewrite sr1 in p1;exact: (h1 _ p1 p3).
  move/free_subsetsP: X0f => [X0sr Xfree].
  have i1: inc (X0 \cap E1) (free_subsets r1).
    apply/free_subsetsP; split;  first by rewrite sr1; apply: subsetI2r.
    by move=> x y /setI2_P[x0 xE1] /setI2_P[y0 yE1]/iorder_gle1 xy;apply:Xfree.
  case: (emptyset_dichot C) => neC.
    move: (p1 _ i1).
    have ->: X0 \cap E1 = X0 by rewrite /E1 /comp neC setC_0; apply/setI2id_Pl.
    rewrite cX0 => /cleNgt; case; exact:(cltS kN).
  have hrec1: order_width r1 k.
    split => //; exists (X0 \cap E1) => //.
    move: (p1 _ i1) => rel1; ex_middle q.
    have : (cardinal (X0 \cap E1)) <c k by split.
    have c1: sub  (X0 \cap E1) X0 by apply: subsetI2l.
    move:(cardinal_setC c1); rewrite cX0 /cdiff.
    set a := cardinal _;  set b := cardinal _.
    have skN: natp (csucc k) by fprops.
    have ca: cardinalp a by rewrite /a; fprops.
    have cb: cardinalp b by rewrite /b; fprops.
    have csa: cardinalp (csucc a) by apply: CS_succ.
    move => p2; rewrite -p2 in skN.
    move: (NS_in_sumr cb skN) (NS_in_suml ca skN) => bN aN.
    move/ (cleSltP aN) /(cleSSP csa (CS_nat kN)). 
    rewrite -p2 (csucc_pr4 csa) (csucc_pr4 ca) - csumA.
    rewrite csum_11 => p3.
    move: (csum_le2l aN NS2 bN p3) => /cle2P [x1 [x2 [x1b x2b x12]]].
    move: x1b x2b => /setC_P [x10] /setI2_P e1 /setC_P [x20] /setI2_P e2.
    move: (X0sr _ x10) (X0sr _ x20) => x1s x2s. 
    case: (inc_or_not x1 C)=> x1C; last by case: e1; split => //; apply /setC_P.
    case: (inc_or_not x2 C)=> x2C; last by case: e2; split => //; apply /setC_P.
    move: torC => [_ ]; rewrite iorder_sr//; move => tc.
    case: (tc _ _ x1C x2C) => h; move: (iorder_gle1 h) => aux.
      by case: x12; move: (Xfree _ _ x10 x20 aux).
      by case: x12; move: (Xfree _ _ x20 x10 aux).
  move: (hrec _ or1 hrec1) =>  [Y [[[uY adi] ane] cY altY]].
  set X:= Y +s1 C.
  have nCY : ~ (inc C Y).
    move=> CY; move: (ane _ CY) => [x xC].
    have : inc x (union Y) by union_tac.
    by rewrite uY sr1 => /setC_P [_ []].
  move: (csucc_pr nCY); rewrite cY -/X => p3.
  have pr1: union X = substrate r.
    rewrite /X;set_extens t.
      move=> /setU_P [y ty /setU1_P]; case => yy; last by  apply: Cs; ue. 
      apply: s1; rewrite - sr1 -uY; union_tac.
     move=> tsr;  apply /setU_P;case: (inc_or_not t C) => tC. 
        by exists C;fprops.
     have : inc t (union Y) by rewrite uY sr1; apply /setC_P. 
     move /setU_P=> [y ty yY]; exists y; fprops.
  have pr2:disjoint_set X.
    move=> a b; case /setU1_P =>  aY; case /setU1_P => bY.
    + by apply: adi.
    + right; rewrite bY; apply: disjoint_pr => u uA.
      have:inc u (union Y) by union_tac.
      by rewrite uY sr1 => /setC_P [_ nxc].
    + right; rewrite aY; apply: disjoint_pr => u uA uB.
      have:inc u (union Y) by union_tac.
      by rewrite uY sr1 => /setC_P [_ nxc].
    + by left; rewrite aY bY.
  have pr3: alls X nonempty. 
    by move=> a; case /setU1_P => ay; [ apply: ane | ue ].
  exists X; rewrite /partition_s; split => //.
  move => x; case /setU1_P => aY; apply/total_subordersP; last by ue.
  move  /total_subordersP: (altY _  aY) =>[]; rewrite iorder_sr // => xe1.
  move: (sub_trans xe1  s1).
  by rewrite /r1 /indC iorder_trans.
(** Let [sra F X] stand for: [X] is a weak partition of [F] of totally ordered
set with at most [k+1] elements. Let [sr C] mean: for any finite set [F], 
there is [X] such that [sra F X] and [C \cap F] is a subset of one element of 
[X]. The previous lemma says that [sr] holds for the empty set.
*)
pose sra F X := [/\ (cardinal X) <=c (csucc k), partition_w X F &
     sub X (total_suborders r)].
pose sr C := sub C (substrate r) /\ forall F, finite_set F ->
    sub F (substrate r) -> exists2 X, sra F X &
     exists2 Y, inc Y X  & sub (C \cap F) Y.
set ssr:= Zo (\Po (substrate r)) sr.
set sso:= sub_order ssr.
move: (sub_osr ssr) => [osso sssr].
have sre: (sr emptyset).
  split; first by fprops.
  move=> F Fsf Fsr.
  set r1:= induced_order r F.
  move: (iorder_osr or Fsr) => [pa pb].
  have fsr1: finite_set (substrate r1) by ue.
  have fk: forall x, inc x (free_subsets r1) 
     -> (cardinal x) <=c (csucc k).
    move=> x  /free_subsetsP[xr1 fs1]; rewrite pb in xr1.
    apply: gensiz; apply/free_subsetsP; split.
      by apply: (@sub_trans F).
   by move=> u v ux vx uv; apply: fs1 => //; apply/iorder_gle0P => //;apply: xr1.
  have skN: natp (csucc k) by fprops. 
  case: (emptyset_dichot F) => eF.
    have pr1:sra F (singleton emptyset).
       rewrite /sra cardinal_set1 /partition_w eF setU_1; split => //.
         apply: cge1; fprops; apply: succ_nz.
        by split => // a b /set1_P -> /set1_P ->; left.
      have s1: sub emptyset (substrate r) by fprops.
      move: (iorder_osr or s1) => [pax pbx].
      move=> a /set1_P ->; apply/total_subordersP; split => //.
      by split; fprops; rewrite iorder_sr//; move=> x y /in_set0.
    exists (singleton emptyset) => //.
    by exists emptyset; fprops; move => t /setI2_P; case.
  move: (order_width_exists fsr1) => [mN' mbd' mp'].
  move: (Exercise4_5b fsr1 pa mN' mp') => [X [[px1 _] xb xc]]; exists X.
    split => //;[ by rewrite xb; move: (proj1 mp') =>[y /fk ya <-] | ue | ].
    by apply: (sub_trans xc); apply:sub_total_suborders1.
  move: eF =>  [u]; rewrite  - pb - (proj1 px1) => /setU_P [y uy yX].
  by ex_tac; move=> t/setI2_P [] /in_set0.
(** The set of subsets satisfying [sr] is inductive. 
  Assume we have sets [Ci], totally ordered by  [sub], and let [C] be the union.
  Let [F] be a finite set, [Vf = C \cap F]. For [x] in [W], there is an index
  [i] such that [x] is in [Ci]. Since [W] is finite, there is a greatest such 
  [Ci]. We deduce [C \cap F = Ci \cap F]. Then [sr C] follows trivially.
*)
have isso: inductive sso.
  move=> X sX tio;rewrite sssr in sX.
  set uX:= union X.
  have uXr: sub uX (substrate r). 
    apply: setU_s2 => y yX t ty.
    move: (sX _ yX) => /Zo_P [] /setP_P ysr _; apply: (ysr _ ty).
  suff uxs: inc (union X) ssr.
    exists (union X); hnf; rewrite sssr; split => //.
    by move=> y yX; apply /sub_gleP;split;fprops;apply: setU_s1.
  apply: Zo_i; [ by apply /setP_P | split => //].
  move => F fsF Fsr; set w := ((union X) \cap F).
  case: (emptyset_dichot w) => wne.
    move: sre; move=> [_ h];  move: (h _ fsF Fsr).
    have -> // : emptyset \cap F = w.
    by rewrite wne; apply /set0_P; move=> y /setI2_P [/in_set0]. 
  pose f x:= choose (fun y => inc x y /\ inc y X).
  have fp: forall x, inc x w -> (inc x (f x) /\ inc (f x) X). 
    move=> x /setI2_P [] /setU_P [y p1 p2] _.
    by apply choose_pr; exists y.
  set w1:= fun_image w f.
  move: (sub_finite_set (@subsetI2r (union X) F) fsF) => fsw.
  move: (finite_fun_image f fsw); rewrite -/w -/w1 => fsw1.
  have sw1: sub w1 X.
    by move => t /funI_P [z zw ->]; case: (fp _ zw).
  have w1ne : nonempty w1.
    move: wne => [x xw]; exists (f x); apply /funI_P; ex_tac.
  have sis: substrate  (induced_order sso X) = X by rewrite iorder_sr//; ue.
  move: (sw1); rewrite - sis => sw2.
  move: sX; rewrite - sssr => sw3.
  move: (sub_trans sw1 sw3) => sw4.
  move: (finite_subset_torder_greatest tio fsw1 w1ne sw2) => [x].
  rewrite iorder_trans //; move=> []; rewrite iorder_sr // => xw1 xle.
  move: (sw1 _ xw1) => xX.
  have ->: w = x \cap F.
    set_extens t.
      move=> tw; apply /setI2_P.
      have ft: inc  (f t) w1 by apply /funI_P; ex_tac.
      move: (xle _ ft) => /(iorder_gle0P _ ft xw1) /sub_gleP [fts xsr ftx].
      move: (fp _ tw) => [pa pb]; split; first by apply: (ftx _ pa).
      by apply: (@setI2_2  (union X)).
   move=> /setI2_P[pa pb]; apply /setI2_P;split => //; union_tac.
  move: (sw3 _ xX); rewrite sssr;move => /Zo_P [_ [_ ok]].
  apply: (ok F fsF Fsr).
(** By Zorn, there is a maximal [C] satisfying [sr]; Taking for [F] a
doubleton shows that [C] is totally ordered *)
move: (Zorn_lemma osso isso) => [C [Cs Cm]].
move: Cs; rewrite sssr => Cs1; move: (Cs1) => /Zo_P [_ [cp1 cp2]].
have toc: inc C (total_suborders r).
  move: (iorder_osr or cp1) => [pax pbx].
  apply:(total_suborder_prop or cp1) => x y xC yC; hnf.
  set F:= doubleton x y.
  have fsF: finite_set F by apply: set2_finite.
  have FC:sub F C by apply: sub_set2.
  have Fsr: sub F (substrate r) by apply: sub_trans cp1.
  move: (cp2 _ fsF Fsr) => [X [pa pb pc]] [Y YX si].
  move /total_subordersP:(pc _ YX) => [ysr [ory]]; rewrite iorder_sr //.
  have xY: inc x Y by apply: si; apply /setI2_P;rewrite /F;split;fprops.
  have yY: inc y Y by apply: si; apply /setI2_P;rewrite /F;split;fprops.
  move=> aux; case: (aux _ _ xY yY) => aux2; move: (iorder_gle1 aux2); fprops.
(** All we need to do is show that free subsets in the complementary of [C]
have at most [k] elements. By contradiction, assume there is [T] with [k+1]
elements. Let [Ci x] be the union of [C] and an element [x] of [T].
By maximality, there exists a finite set [Ciq x], denoted here [F] such that
for any [X] such that [sra X] holds, for any [Y] in [X], [(Ci x) \cap F] is
not a subset of [Y]. Let [G] be the union of these sets, together with [T].
 *)
case: (p_or_not_p (forall T,
      sub T (comp C) -> free_subset r T -> (cardinal T) <=c k)) => hh.
   by exists C.
case: hh => T TC fsT.
have Tc: sub T (substrate r).
  apply: (@sub_trans  (comp C)) => //; apply: sub_setC.
have Tf: inc T (free_subsets r) by apply/free_subsetsP.
move: (gensiz _ Tf); case: (equal_or_not  (cardinal T) (csucc k)); last first.
  move=> pa pb; apply /cltSleP => //; split => //. 
move => cTk _.
pose Ci i := C +s1 i.
pose Cip i F :=  finite_set F /\ sub F (substrate r)
    /\ forall X, sra F X -> forall Y, inc Y X ->
     ~ ( sub ((Ci i) \cap F) Y).
have Cip1: forall i, inc i T -> exists F, Cip i F. 
  move=> i iT; case: (p_or_not_p (gle sso C (Ci i))) => h.
    move: (TC _ iT) => /setC_P [_]; rewrite - (Cm _ h); case; apply: setU1_1.
  ex_middle ef; case: h.
  have cc: sub C (Ci i) by apply: sub_setU1.
  have cc2: sub (Ci i) (substrate r) by apply: setU1_sub => //; apply: Tc.
  apply /sub_gleP;split=> //;apply/ Zo_P; split;first by apply /setP_P.
  split => // F Fsf Fsr; ex_middle exp.
  case: ef; exists  F;rewrite /Cip;split => //; split => // X p1 Y YX. 
  case: (p_or_not_p (sub ((Ci i) \cap F) Y)) => //.
  move =>  bad2; case: exp; exists X => //; ex_tac.
pose Ciq i := choose (fun F => Cip i F).
have Cip2: forall i, inc i T -> Cip i (Ciq i).
  by move => i iT; apply: choose_pr; apply: Cip1.
set G:= T \cup (unionb (Lg T Ciq)).
have fG: finite_set G.
  apply: finite_union2; first by rewrite /finite_set cTk ; apply /NatP; fprops.
   apply: finite_union_finite; fprops; hnf; aw.
     by move=> i iT; rewrite LgV//; move: (Cip2 _ iT) => [Ok _].
   hnf; rewrite cTk;  apply /NatP; fprops.
have Gs: sub G (substrate r).
  rewrite /G=> t; case /setU2_P;  first by apply: Tc.
  move /setUb_P;aw; move=> [y yd]; rewrite LgV//  => tC.
  by move: (Cip2 _ yd) => [_ [Ok _]]; apply: Ok.
(** By construction there is a partition [X] of [G], and [Y] such that
 [C \cap G] is a subset of [Y]. We have [sra ( Ciq i) (mp i)], where [mp i]
 is the set of intersections of [Ciq i] with the elements of [X].
 *)

move: (cp2 _ fG Gs) => [X [cX [uX mdX] toX] [Y YX si]].
pose mp i := fun_image X (fun k => (Ciq i) \cap k).
have Cip3: forall i, inc i T -> sra (Ciq i) (mp i).
  move=> i iT.
  have pr1:cardinal (mp i) <=c csucc k.
    set fa:= Lf (fun k => (Ciq i) \cap k) X (mp i).
    have ff: function fa. 
      apply: lf_function; move=> t tX; apply /funI_P; ex_tac.
    move: (image_smaller ff).
    rewrite /fa; aw; set y := Imf _.
    have ->: y = (mp i).
      rewrite /y /mp/Imf lf_source.
      set Ta := [eta intersection2 (Ciq i)]. 
      have aa: sub X (source (Lf Ta X (fun_image X Ta))) by aw.
      have bb: lf_axiom Ta X (fun_image X Ta) 
           by move=> t tx; apply /funI_P; ex_tac.
      set_extens t. 
        move /(Vf_image_P ff aa) => [z pa pb]; apply /funI_P; ex_tac.
        rewrite pb /fa LfV//.
      move /funI_P => [z pa pb] ;apply /(Vf_image_P ff aa); ex_tac.
      rewrite pb /fa LfV//.
    move=> le1; exact:(cleT le1 cX).
  have pr2: union (mp i) = Ciq i.
    set_extens t. 
      move=> /setU_P [y ty] /funI_P [z zX izy]. 
      by apply:(@setI2_1 _ z); rewrite - izy.
    move=> ti; apply /setU_P.
    have: inc t G.
      apply /setU2_P; right; apply /setUb_P; aw; exists i => //;rewrite LgV//.
    rewrite -uX => /setU_P [y ty yX].
    exists ((Ciq i) \cap y) => //; first by apply /setI2_P. 
    apply /funI_P; ex_tac.
  have pr3:disjoint_set (mp i).
    move=> a b /funI_P [za zaX ->] /funI_P [zb zbX ->]. 
    case: (mdX _ _ zaX zbX); first by  move=> ->; left.
    rewrite {1}/disjoint; right; apply: disjoint_pr => u.
    by move=> /setI2_P [_ ua] /setI2_P [_ ub]; empty_tac1 u; apply: setI2_i.
  split => // Y1 /funI_P [z zX ->]. 
  have aux1: sub ((Ciq i) \cap z) z by apply: subsetI2r.
  exact:(sub_total_suborders2 or (toX _ zX) aux1).
(** The sets [T] and [Y] are disjoint. But [T] intersects each element of [X]
at most once, thus exactly once, absurd. *)

have TYe: T \cap Y = emptyset.
  apply /set0_P => y /setI2_P [yT yY].
   move: (Cip2 _ yT) => [pa [pb pc]]; move: (pc _ (Cip3 _ yT)) =>  aux.
   have YMP: inc ((Ciq y) \cap Y) (mp y) by apply /funI_P; ex_tac.
  case: (aux _ YMP) => t /setI2_P [ta tb]; apply /setI2_P;split => //.
  move: ta; case /setU1_P; last  move=> ->; fprops.
  move=> tC;apply: si; apply /setI2_P;split => //; apply /setU2_P;right.
  apply /setUb_P; aw; ex_tac; rewrite LgV//.
have stu: sub T (union X) by rewrite uX /G; apply: subsetU2l.
set k1:= cardinal X.
have ksb: natp (csucc k) by fprops.
have k1N: natp k1 by apply: (NS_le_nat cX ksb).
move:cX; rewrite - cTk =>/eq_subset_cardP1/set_leP [T1 T1S]. 
move/card_eqP/esym; rewrite -/k1 => pa.
have sm:(forall Z : Set, inc Z X -> small_set (T1 \cap Z)).
  move=>  Z ZY x y /setI2_P [xT xZ] /setI2_P [yT yZ].
  move: (T1S _ xT)  (T1S _ yT) => xt1 yt1.
  have Zr': sub Z G by rewrite -uX; apply: setU_s1.
  move/total_subordersP: (toX _ ZY) => [Zr [orZ]]; rewrite iorder_sr// => tor. 
  case: (tor _ _ xZ yZ)=> aux.
    by move: (iorder_gle1 aux); apply: fsT.
    by symmetry; move: (iorder_gle1 aux); apply: fsT.
move: ((@Exercise4_5a X T1 k1 (refl_equal (cardinal X)) pa k1N
   (sub_trans T1S stu) mdX sm) _ YX).
move=> [x]; aw => sx; move: (set1_1 x); rewrite - sx.
move=> /setI2_P [ha hb]; empty_tac1 x; aw; split => //.
Qed.





(** ----  Exercise 4.6.
We start with some follow-ups to the previous exercise.
The notations [H], [Hw], [C] and [Cw] are as above. We first show that a 
non-empty bounded set of integers has a greatest element. 
It follows that if [Hw(n)] holds, then [H(k)] holds for some [k].
If [Hw(n+h)] holds and there is a free subset with [n] elements, 
then [H(n+k)] holds for some [k].
 *)

(* virer apres CI
Lemma finite_bounded_greatest_B n T:
  natp n -> (forall m, inc m T -> m <=c n) ->
  nonempty T ->
  exists2 m, inc m T & forall k, inc k T -> k <=c m.
Proof.
move => nN; move: n nN ; apply: Nat_induction.
  move => H [x xT]; ex_tac => k /H /cle0 ->.
  move /H: xT => /cle0 ->; fprops.
move => n nN Hrec h ne; case: (inc_or_not (csucc n) T) => sT; first by ex_tac.
apply: Hrec => // m mT; apply/(cltSleP nN); split; [ by apply:h | dneg w; ue].
Qed.

Lemma finite_bounded_greatest_B_alt n T:
  natp n -> (forall m, inc m T -> m <=c n) ->
  nonempty T ->
  exists2 m, inc m T & forall k, inc k T -> k <=c m.
Proof.
move=> nN Tp neT.
have zb:= NS0.
have Ti: sub T (Nintcc \0c n).
  by move=> i iT; bw; move: (Tp _ iT) => lein;  apply /NintcP.
have aux: Nat_le \0c n by  split; fprops; apply/cle0n. 
move: (sub_finite_set Ti (finite_Nintcc \0c n)) => fst.
move: (Ninto_wor \0c n) => [/worder_total iot sio].
rewrite - sio in Ti.
move: (finite_subset_torder_greatest iot fst neT Ti) => [x []].
move: iot=> [ot _];aw => xT aux2; ex_tac.
move=> k kT; move: (iorder_gle1 (aux2 _ kT)).
by move /Ninto_gleP => [_ _].
Qed.
*)  



(** Assumptions: we have two non-empty families [X] and [Y] with [m] and [n] 
elements. Let [E46_hprop h] be the property that, whenever we take 
[r+h] elements of [X], the union of these sets meets at least [r] elements 
of [Y]. Let [E46_h h] be the property that [h] is the least integer satisfying
this property. Then there is a set with at most [n+h] elements that meets
every element of [X] and [Y].

For simplicity, we assume the domains of [X] and [Y] disjoint, 
and we define an ordering
on the union of the domains such that [i<j] if [X(i)] meets [Y(j)].
*)


Section Exercise46.
Variables A X Y m n :Set.
Hypothesis (nN: natp n) (mN: natp m). 
Hypothesis Xpr:
  [/\ fgraph X, cardinal (domain X) = m, sub (range X) (\Po A) &
  nonempty_fam X].
Hypothesis Ypr:
  [/\ fgraph Y, cardinal (domain Y) = n, sub (range Y) (\Po A) &
   nonempty_fam Y].
Hypothesis disdom: disjoint (domain X) (domain Y).

Definition E46_hprop h := forall r  Z, r <=c (m -c h) ->
   sub Z (domain X) -> cardinal Z = r +c h  ->
   exists T, [/\ sub T (domain Y),  cardinal T = r &
   forall j, inc j T -> meet (Vg Y j) (unionb (restr X Z))]. 

Definition E46_hp h :=  [/\ natp h, h <=c m,  E46_hprop h &
   forall l, natp l ->  l <=c m -> E46_hprop l -> h <=c l].

Definition E46_conc h := exists B, [/\ (cardinal B) <=c (n +c h),
  finite_set B, allf X (meet B) &allf Y (meet B)].

Definition E46_u := (domain X) \cup (domain Y).
Definition E46_order_rel x y := 
  x = y  \/ [/\ inc x (domain X), inc y (domain Y) & meet (Vg X x) (Vg Y y)].
Definition E46_order_r :=  graph_on E46_order_rel  E46_u.


Lemma Exercise4_6a:
  order_on E46_order_r E46_u  /\
  (forall x y, gle E46_order_r x y <->
    [/\ inc x E46_u, inc y E46_u & E46_order_rel x y]).
Proof.
have pa: (forall a, inc a  E46_u -> E46_order_rel a a).
  by move => a _; left.
move: (graph_on_sr pa); rewrite -/E46_order_r => sr.
have or: order E46_order_r. 
  apply: order_from_rel;split => //.
      move=> y x z; case => xy; first (by rewrite xy); case => yz => //. 
        by rewrite -yz; right.
      move: xy yz => [_ yY _][yX _ _];empty_tac1 y.
    move => x y; case => // xy;  case => // yx. 
    move: xy yx => [_ yY _][yX _ _]; empty_tac1 y.
  by move => x y _; split; left.
split => //; move=> x y; apply /graph_on_P1.
Qed.

(**  We show that there is [h] such that [E46_hp h] holds  *)

Lemma Exercise4_6b h: h <=c m ->
  E46_hprop h ->  m <=c (n +c h).
Proof. 
move =>  hm hp; move: (NS_le_nat hm mN) => hN.
move: (NS_diff h mN)(cdiff_pr hm); set r := (m -c h); move=> rN phm.
have pa: r <=c (m -c h) by rewrite -/r; fprops. 
have pb: sub (domain X) (domain X) by fprops. 
have pc: cardinal (domain X) = r +c h.
   by rewrite csumC phm; move: Xpr => [_ ok _ _].
move: (hp _ _ pa pb pc) => [T [Td cT _]].
move: (sub_smaller Td); move: Ypr => [_ cdY _ _]; rewrite cT cdY.
have lehh: h <=c h by fprops.
by move=> pd; move: (csum_Mlele pd lehh); rewrite csumC phm.
Qed.


Lemma  Exercise4_6c: exists h,  E46_hp h.
Proof.
have hm: E46_hprop m.
  move=> r Z le1 Zd cT.
  exists emptyset;split;fprops;last by move=> j /in_set0.
  rewrite (cdiff_nn m) in le1.
  rewrite (cle0 le1) cardinal_set0 //.
move: (least_int_prop (p:= E46_hprop) mN hm).
set y := (least_ordinal E46_hprop m); move => [yN hy yl].
exists y; split; fprops.
Qed.


(** We restate [E46_hprop h] as a property of the ordering *)

Lemma Exercise4_6d h:  E46_hprop h <->
  forall r Z,  r <=c (m -c h) ->
   sub Z (domain X) -> cardinal Z = r +c h  ->
   exists T, [/\ sub T (domain Y),  cardinal T = r &
   forall j, inc j T -> exists2 i, inc i Z & gle E46_order_r i j].
Proof.
move: Exercise4_6a Xpr  => [[oR sR] rR]  [fgX _ _ _].
split; move=> aux r Z pa pb pc;
  move: (aux _ _ pa pb pc) => [T [tdY cT aux1]]; exists T;split => // j jT.
  move: (aux1 _ jT) => [k] /setI2_P [kVg] /setUb_P [y].
  rewrite restr_d // => yd; rewrite restr_ev//.
  have yX: inc y (domain X) by apply: pb. 
  have jY: inc j (domain Y)  by apply: tdY.
  move=> kV1; ex_tac; apply/rR;rewrite /E46_u; split;fprops.
  by right; split => //;exists k; apply: setI2_i.
move: (aux1 _ jT) => [i iZ]; move / rR => [_ _ ].
case => h0.
  empty_tac1 j;rewrite -h0; fprops.
move: h0 => [_ _ [k]] /setI2_P [k1 k2]; exists k; apply /setI2_P;split => //.
apply /setUb_P; exists i; rewrite ?restr_d //; rewrite restr_ev//.
Qed.

(** Proprety [E46_hprop h] says that free subsets are not too big  *)

Lemma Exercise4_6e h K: 
  natp h -> E46_hprop h -> inc K (free_subsets E46_order_r) ->
  (cardinal K) <=c (n +c h).
Proof.
move=> hN /Exercise4_6d  aux free.
set Z :=  K \cap (domain X).
set Z1 := K \cap (domain Y).
have ZX: sub Z (domain X) by apply: subsetI2r.
have Z1Y: sub Z1 (domain Y) by apply: subsetI2r.
move: Exercise4_6a => [[oR sR] rR].
case /free_subsetsP:free ;rewrite sR /E46_u; move=> pa pb.
have uZ: K = Z \cup Z1.
  rewrite - (set_IU2r K (domain X) (domain Y)).
  by symmetry; apply /setI2id_Pl.
have dj: disjoint Z Z1.
   apply: disjoint_pr => u ux uy; empty_tac1 u; saw.
move: (csum2_pr5 dj); rewrite -uZ - csum2cr - csum2cl => cs.
move:(proj42 Xpr) (proj42 Ypr) => cX cY.
have cZN: natp (cardinal Z). 
  have fsdX: finite_set (domain X) by hnf; rewrite cX; apply /NatP.
  by move: (sub_finite_set ZX fsdX) =>  /NatP.
case: (NleT_ee cZN hN) => le1.
  move: (sub_smaller Z1Y) => aux1; move: (csum_Mlele le1 aux1).
  by rewrite - cs csumC cY.
move:(NS_diff h cZN)(cdiff_pr le1);set r := (_ -c h); move=> rN phm.
move: (sub_smaller ZX); rewrite cX => Zm.
have c2:cardinal Z = r +c h by symmetry; rewrite csumC.
rewrite cs c2 csumC csumA.
apply: csum_Mlele; last by fprops.
have c1: r <=c (m -c h).
   rewrite -phm in Zm; apply: (csum_le2l hN) => //; fprops.
   rewrite cdiff_pr //.
   by apply: cleT Zm; apply: csum_M0le; fprops.
move: (aux _ _ c1 ZX c2) => [T [TdY cT etc]].
have di: disjoint Z1 T.
  apply: disjoint_pr => j jZ1 jT; move: (etc _ jT) => [i iZ le].
  have iK: inc i K by rewrite uZ; apply /setU2_P; left.
  have jK: inc j K by rewrite uZ; apply /setU2_P; right.
  move: (pb i j iK jK le) => ij.
  by empty_tac1 i; rewrite ij.
move:(csum2_pr5 di); rewrite - cY - cT csum2cr csum2cl => <-.
apply: sub_smaller; move=> t; case /setU2_P => ta; fprops.
Qed.

(** Property [E46_hp h] says [H(n+k)] for some [k] *)

Lemma Exercise4_6f h: natp h -> E46_hprop h ->
  exists k, [/\ natp k, k <=c h & order_width E46_order_r  (n +c k)].
Proof.
move=> hN hp.
set r := E46_order_r.
have hyp1: (forall x, inc x  (free_subsets r) -> (cardinal x) <=c (n +c h)). 
  by move=> t ts;apply: Exercise4_6e.
have [x xf cx]:(exists2 x, inc x(free_subsets E46_order_r) & (cardinal x = n)).
  move: Exercise4_6a => [[oR sR] rR].
  exists (domain Y).
    apply /free_subsetsP; split; first by rewrite sR /E46_u; apply: subsetU2r.
    move=> x y; rewrite rR; move=> xY yY [_ _ ]; case => //; move=> [xX _].
    empty_tac1 x. 
  by move: Ypr => [_ pa _].
have nef: nonempty (free_subsets r) by ex_tac.
move: (the_max_card_on_set_prop  (NS_sum nN hN) nef hyp1).
set k := the_max_card_on_set _; move => [[qa qb] kN].
move: (qb _ xf); rewrite cx => lexk.
move: (NS_diff n kN)(cdiff_pr lexk).
move => kcN aux; exists (k -c n); split => //; last by rewrite aux.
move: qa => [y ys yx]; move: (hyp1 _ ys); rewrite yx -{1} aux.
move=> aux3; apply: (csum_le2l nN) => //.
Qed.

Lemma Exercise4_6g h: E46_hp h ->
  exists k, [/\ natp k, k <=c h & Exercise4_5_conc E46_order_r  (n +c k)].
Proof.
move=> [hN _ hprop _]; move: (Exercise4_6f hN hprop).
move=> [k [kN pa pb]]; exists k; split => //.
move: Exercise4_6a => [[oR sR] rR].
exact: (Exercise4_5d oR (NS_sum nN kN)  pb).
Qed.

(** We apply the previous exercise. It gives a partition of [E] into totally 
ordered  sets. Note that an ordered set [U] is either [singleton A], where [A]
is in [X] or [Y], or a doubleton 
[(A,B)] where [A] is in [X] and [B] in [Y], and these sets meet; let [xU] be
an element of [A] in the first case, an element of [A \cap B] in the second case.
The set of these [xU] is a solution.*)

Lemma Exercise4_6h h: E46_hp h ->  E46_conc h.
Proof.  
move=> hp; move: (Exercise4_6g hp) => [k [kN kh [C [pC cc altc]]]]. 
move: pC => [[pca pcc] pcb].
move: Exercise4_6a => [[oR sR] rR].
hnf in disdom.
have tcp: forall x a b, inc x C -> inc a x -> inc b x ->
   [\/ a = b, glt E46_order_r a b | glt E46_order_r b a].
  move=> x a b xC ax bx; case: (equal_or_not a b) => nab; first by in_TP4.
  have nba: b <> a by apply:nesym.
  move /total_subordersP: (altc _ xC) => [sxs [or]].
  rewrite iorder_sr //; move => aux; move: (aux _ _ ax bx).
  by case => aux2; [constructor 2 | constructor 3]=> //;move:(iorder_gle1 aux2).
have tcp1: forall i j,  glt E46_order_r i j ->
  [/\ inc i (domain X), inc j (domain Y) & meet (Vg X i) (Vg Y j)].
  move=> i j [leij nij]; move: leij;rewrite  rR;  move =>  [isR jsR].
  case => h0 //.
have tcp2: forall x, inc x C ->
  [\/ (exists2 i, inc i (domain X) &  x = singleton i),
      (exists2 j, inc j (domain Y) &  x = singleton j) |
      (exists i j, glt E46_order_r i j /\ x = doubleton i j)].
  move=> x xC; move: (pcb _ xC) => xne.
  move: (xne) => [y yx].
  case: (equal_or_not x (singleton y)) => xs.
    have: inc y (union C) by union_tac.
    rewrite pca sR /E46_u. 
    case /setU2_P => yc; [constructor 1 | constructor 2 ]; ex_tac.
  have [z zx yz]: exists2 z, inc z x & y <> z.
    ex_middle bad; case: xs; apply set1_pr => // z zx.
    ex_middle ty; case: bad; exists z;fprops.
  have [i [j [ix jx ltij]]]: exists i  j, [/\ inc i x, inc j x & 
    glt E46_order_r i j].
    case: (tcp _ _ _ xC yx zx); first (by contradiction); case => h0.
       by exists y, z.
     by exists z, y.
  move: (tcp1 _ _ ltij)  => [iX jY _].
  constructor 3; exists i, j; split => //. 
  set_extens t; last by case /set2_P => ->.
  move => tx; case: (tcp _ _ _ xC tx ix); first by move => ->; fprops.
    by move => ti; move: (tcp1 _ _ ti)  => [_ iY _]; empty_tac1 i; aw. 
  case: (tcp _ _ _ xC jx tx); first by move => ->; fprops.
    by move => tj; move: (tcp1 _ _ tj)  => [jX _]; empty_tac1 j; aw. 
  move => ti tj; move: (tcp1 _ _ ti)  (tcp1 _ _ tj) => [tX _ _] [_ tY _].
  empty_tac1 t. 
pose xup x y:= forall i,
    ( (inc i (x \cap (domain X)) -> inc y (Vg X i) ) /\
      (inc i (x \cap (domain Y)) -> inc y (Vg Y i))).
pose f x := choose (fun y => xup x y).
have fp1: forall x, inc x C -> xup x (f x).
  move=> x xc; apply: choose_pr; case: (tcp2 _ xc).
      move => [i idX ->]; exists (rep (Vg X i)); hnf.
      move=> j;split; move => /setI2_P [] /set1_P -> uu.
        by apply: rep_i;move: Xpr => [_ _ _ hh]; apply: hh.
      empty_tac1 i; apply /setI2_P;split => //.
    move => [i idX ->]; exists (rep (Vg Y i)); hnf.
    move=> j; split;  move => /setI2_P [] /set1_P -> uu.
      by empty_tac1 i; aw.
    by apply: rep_i;move: Ypr => [_ _ _ hh]; apply: hh.
  move=> [i [j [ltij]]] ->; move: (tcp1 _ _ ltij) => [idx jdy mt].
  exists (rep ((Vg X i) \cap (Vg Y j))).
  move: (rep_i mt) => /setI2_P; set r:= rep _; move=> [ra rb].
  move => z;aw;split; move => /setI2_P [];case /set2_P => -> bad //.
    by empty_tac1 j; aw.
  by empty_tac1 i; aw.
set B:= fun_image C f.
have pa: (cardinal B) <=c (n +c h).
  have sjb: (surjection (Lf f C (fun_image C f))). 
    apply: lf_surjective; first by move=> t ta; apply /funI_P; exists t.
    move=> y /funI_P //.
  move: (image_smaller (proj1 sjb)); rewrite (surjective_pr0 sjb). 
  aw; rewrite -/B => l1; apply:(cleT l1).
  rewrite cc; apply: csum_Mlele => //; fprops.
have pb: finite_set B.
  move: hp => [hN _ _ _].
  hnf; apply /NatP; apply: (@NS_le_nat _ (n +c h)); fprops.
have sBA: sub B A.
  move=> t /funI_P [z zC ->]; move: (fp1 _ zC) => fz.
  move: Xpr Ypr => [fgX _ rpX _][fgY _ rpY _].
  have auxx: forall i y, inc i (domain X) -> inc y (Vg X i) -> inc y A.
    move=> i y id yv.
    suff: sub (Vg X i) A by apply.
    apply /setP_P; apply: rpX; apply /(range_gP fgX); ex_tac.
  have auxy: forall i y, inc i (domain Y) -> inc y (Vg Y i) -> inc y A.
    move=> i y id yv.
    suff : sub (Vg Y i) A by apply.
    apply /setP_P; apply: rpY; apply /(range_gP fgY); ex_tac.
  case: (tcp2 _ zC).
      move=> [i idx zi].
      have ii2: inc i (z \cap (domain X)) by rewrite zi; fprops.
      move: (fz i) => [fa _]; move: (fa ii2) => fv; apply: (auxx _ _ idx fv).
    move=> [i idx zi]. 
    have ii2: inc i (z \cap (domain Y)) by rewrite zi; fprops.
    move: (fz i) => [_ fa]; move: (fa ii2) => fv; apply: (auxy _ _ idx fv).
  move=> [i [j [ltij zi]]];  move: (tcp1 _ _ ltij) => [idx jdy mt].
  have ii2: inc j (z \cap (domain Y)) by rewrite zi; fprops.
  move: (fz j) => [_ fa]; move: (fa ii2) => fv; apply: (auxy _ _ jdy fv).
exists B; split => // i idx.
  have : inc i (union C) by rewrite pca sR /E46_u; fprops.
  move=> /setU_P [y iy yC]; move: (fp1 _ yC i) => [fa _].
  move: (fa (setI2_i iy idx)) => pc.
  exists (f y); apply /setI2_P;split => //; apply /funI_P; ex_tac.
have : inc i (union C) by rewrite pca sR /E46_u; fprops.
move=> /setU_P [y iy yC]; move: (fp1 _ yC i) => [_ fa].
move: (fa (setI2_i iy idx)) => pc.
exists (f y);  apply /setI2_P;split => //;  apply /funI_P; ex_tac.
Qed.
End Exercise46.

(** Assume [A(x)] is a subset of [F] for any [x] in [E]. We want to know when
 [ E46b_hyp ] holds, namely that there exists an injection [f] such that 
 [f(x)] is in [A(x)], or when [ E46c_hyp G] holds (this is [ E46b_hyp ], where 
 moreover [G]  is a subset of the image of [f].

Let [E46b_conc] be the assertion: for any set [H], the union of all [A(x)], 
for  [x] in [H] has at least as many elements as [H], and let [E46c_conc G]
be: for any subset [L] of [G], the number of elements [x] such that [A(x)]
meets [L] is at least the cardinal of [L].

We have:  [E46b_hyp] implies [E46b_conc], and  [E46c_hyp G] implies
[E46b_conc] and [E46c_conc G].
 *)

Definition E46b_hyp E F A := 
  exists2 f, injection_prop f E F &
  (forall x, inc x E -> inc (Vf f x) (A x)).

Definition E46c_hyp E F A G := 
  exists f, [/\ injection_prop f E F,
  sub G (Imf f) &  (forall x, inc x E -> inc (Vf f x) (A x))].

Definition E46b_conc E A := 
  forall H, sub H E -> 
  (cardinal H) <=c (cardinal (union (fun_image H A))). 

Definition E46c_conc E A G := 
  forall L, sub L G -> 
    (cardinal L) <=c (cardinal (Zo E (fun z => meet (A z) L))).


Lemma Exercise4_6i E F A:  E46b_hyp E F A -> E46b_conc E A.
Proof.
move=>  [f [injf sf tf] fp] H HE.
have ff: function f by fct_tac.
have shs:sub H (source f) by ue.
have pa:sub (Vfs f H) (union (fun_image H A)).
  move=> t /(Vf_image_P ff shs) [u uH ->].
  move: (fp _ (HE _ uH)) => aux; apply /setU_P;exists (A u) => //.
  apply /funI_P; ex_tac.
move: (sub_smaller pa) => pb.
move: (Eq_restriction1 shs injf).
by move /card_eqP => ->.
Qed.

Lemma Exercise4_6j E F A G:  E46c_hyp E F A G ->
  (E46b_conc E A /\  E46c_conc E A G).
Proof.
move =>  [f [[injf pa pb] pc pd]].
split; first by apply: (@Exercise4_6i _ F) ; exists f => //.
move => L LG; set K := Vfi f L.
have ff: function f by fct_tac.
have Ksf: sub K (source f).
  move=> t /iim_graph_P [u uL Jg]; Wtac.
have aux: L = Vfs f K.
   set_extens t.
    move => tL; apply /(Vf_image_P ff Ksf).
    move: (pc _ (LG _ tL)) =>  /(Imf_P ff) [x xsf Jg]. 
    exists x => //; apply /iim_graph_P; exists t => //; rewrite Jg; Wtac.
  move /(Vf_image_P ff Ksf) => [u ui ->]; move:ui => /iim_graph_P [v vL Jg].
  by rewrite - (Vf_pr ff Jg).
move: (Eq_restriction1 Ksf injf). 
rewrite -aux; move /card_eqP=> <-; apply: sub_smaller. 
move => t /iim_graph_P [u uL jg]; move: (p1graph_source ff jg) => tf. 
rewrite pa in tf;apply: Zo_i => //; move: (pd _ tf); rewrite - (Vf_pr ff jg).
by move=> ua; exists u; apply /setI2_P.
Qed.


(** Converse:  [E46b_conc] and [E46c_conc G] imply [E46b_conc]
if [E] and [F] are finite *)

Lemma Exercise4_6k E F A G:
  finite_set F -> sub G F ->
  (forall x, inc x E -> sub (A x) F) ->
   E46b_conc E A ->  E46c_conc E A G -> E46b_hyp E F A.
Proof.
move=> fsF GF Ap h1 h2.
(** we consider some ordering on the disjoint union of [E], [F] and [G] *)
set Gi:= G *s1 C0.
set Fi:= F *s1 C1.
set Ei:= E *s1 C2.
set Et := Gi \cup (Fi \cup Ei).
have Gp1: forall x, inc x G -> inc (J x C0) Et.
   by move=> x xG; apply /setU2_P;left; apply:indexed_pi.
have Fp1: forall x, inc x F -> inc (J x C1) Et.
  by move=> x xG; apply /setU2_P;right; apply /setU2_P;left;  apply:indexed_pi.
have Ep1: forall x, inc x E -> inc (J x C2) Et.
  by move=> x xG;apply /setU2_P;right; apply /setU2_P;right;  apply:indexed_pi.
pose rc x y := [\/ x = y, [/\ Q x = C0, Q y = C1 & P x = P y]  |
    [/\ (Q x = C0 \/ Q x = C1), Q y = C2 & inc (P x) (A (P y))]].
set r := graph_on rc Et.
have sr: substrate r = Et by apply: graph_on_sr; move=> a _; in_TP4.
have rvP: forall x y, gle r x y <-> [/\ inc x Et, inc y Et & rc x y].
  by move=> x y; apply /graph_on_P1.
move: C0_ne_C1 C2_ne_C01 => n01 [n20 n21].
have trr: transitive_r rc.
  move => x y z xy; case: (xy); first by move=> ->.
    move=> aux; case; first by move=> <-.
      by move: aux => [_ pa _] [pb _ _]; case: n01; rewrite - pa - pb.
    move => [a2 pa pb]; case: a2. 
      by move => a2; case: n01; rewrite -a2; move : aux => [_ -> _].
    by move: aux => [pc pd pe] h; constructor 3; rewrite pe; split => //; left.
  move=> [pa pb pc]; case; first by move => <-.
    by move => [pd _ _]; case: n20; rewrite -pb -pd.
  by rewrite pb;move => [pd _ _];case: pd => pd; [ case: n20 | case: n21].
have arr: antisymmetric_r rc.
  move => x y xy; case: xy; first by move=> ->.
    move=> aux; case; first by move=> <-.
      by move: aux => [_ pa _] [pb _ _]; case: n01; rewrite - pa - pb.
    by move: aux => [pa _ _] [_ pb _]; case: n20; rewrite - pa - pb.
  move=> [_ pb _]; case; first by move => <-.
    by move => [pd _ _]; case: n20; rewrite -pb -pd.
  by rewrite pb;move => [pd _ _];case: pd => pd; [ case: n20 | case: n21].
have or: order r. 
  apply: order_from_rel;split => //.
  by move=> x y _; split; constructor 1.
(** We consider the size of the biggest free subset *)
set m := cardinal F.
have pa: (exists2 x, inc x (free_subsets r) & cardinal x = m).
  exists Fi; last by rewrite (cardinal_indexed F C1). 
  apply: Zo_i; first by apply /setP_P; rewrite sr /Et => t; fprops.
  move=> x y xFi yFi; move: xFi yFi=> /indexed_P  [_ _ qx] /indexed_P [_ _ qy].
  move /rvP => [_ _]; case  => //.
    by move=> [qxa _]; case: n01; rewrite -qx -qxa.
  by move=> [_ qya _]; case: n21; rewrite -qy -qya.
have pb: forall x, inc x Et -> pairp x.
  by move => x;case /setU2_P; [ | case /setU2_P];  move/indexed_P => [].
have pc: order_width r m.
  split => // x0 => /Zo_P [] /setP_P; rewrite sr; move=> xET x0f.
  pose f x := Yo (Q x = C0) (J (P x) C1) x.
  set x1 := fun_image x0 f.
  have x1E: sub x1 Et.
    rewrite /x1; move=> t /funI_P [z zx0 ->].
    move: (xET _ zx0) => zEt; rewrite /f; Ytac zza => //;apply: Fp1.
    move: (zEt); case /setU2_P.
      by move /indexed_P => [_ hh _]; apply: GF.
    by case /setU2_P;move/indexed_P => [_ h3 h4]//;case: n20;rewrite -h4 - zza.
  have x1f: free_subset r x1.
    move=> x y /funI_P [u ux0 ->]  /funI_P [v vx0 ->] h.
    case: (equal_or_not u v) => nuv; first by rewrite nuv.
    move: (xET _ ux0)(xET _ vx0) => uEt vEt.
    move: h;rewrite /f; Ytac uza; Ytac vza.
    + by move /rvP=> [_ _]; case => //;aw;
             move => [xx yy]; [case: n01 | case: n21].
    + move /rvP => [_ _]; case => //; aw; first by move => [p1]; case: n01.
      move => [_ aa bb].
      case: nuv;apply: (x0f u v ux0 vx0); apply /rvP; split => //.
      by constructor 3; split => //; left.
    + by move /rvP => [ _ _]; case => //; aw; move => [aa /esym bb].
    + by move=> uv;case: nuv; apply: (x0f u v).
  have -> : cardinal x0 = cardinal x1.
    apply /card_eqP; exists (Lf f x0 x1); saw; apply: lf_bijective.
        move=> t tx0; apply /funI_P; ex_tac.
      move=> u v ux0 vx0; rewrite /f;  Ytac uza; Ytac vza.
      + move: (pb _ (xET _ ux0)) (pb _ (xET _ vx0)) => xp yp sJ.
        apply: pair_exten => //; [apply: (pr1_def sJ) | ue ].
      + move=> sj; move: (f_equal P sj) (f_equal Q sj); aw => qa qb.
        by apply: (x0f u v) => //; apply /rvP;split;fprops; constructor 2.
      + move=> sj; move: (f_equal P sj) (f_equal Q sj); aw => qa qb.
        by symmetry;apply:(x0f v u)=>//; apply /rvP;split;fprops; constructor 2.
      + done.
    by move=> y/funI_P.
  set H1 := Zo E (fun z => inc (J z C2) x1).
  set H2 := Zo F (fun z => inc (J z C1) x1).
  have ->: cardinal x1 = (cardinal H1) +c (cardinal H2).
    have ->: x1 = (x1 \cap Ei) \cup (x1 \cap Fi).
    rewrite - (set_IU2r x1 Ei Fi); symmetry; apply /setI2id_Pl.
    move => t; case /funI_P => [z zx0 ->].
       move: (xET _ zx0); case /setU2_P.
         move /indexed_P => [pz Pz Qz]; apply /setU2_P; right. 
         by rewrite /f; Ytac0; apply: indexed_pi; apply: GF.
       case /setU2_P; move /indexed_P => [pz Pz Qz]; rewrite /f.
         rewrite Qz; Ytac0; apply /setU2_P; right; by apply /indexed_P.
         rewrite Qz; Ytac0; apply /setU2_P; left; by apply /indexed_P.
    rewrite csum2cl csum2cr.
    have di: disjoint (x1 \cap Ei) (x1 \cap Fi).
      by apply: disjoint_pr; move  => u /setI2_P [_] /indexed_P [_ _ qc]
       /setI2_P [_] /indexed_P[_ _ qb]; case: n21; rewrite - qc -qb.
    rewrite (csum2_pr5 di); apply: csum2_pr2; apply/card_eqP.
       exists (Lf P (x1 \cap Ei) H1).
        saw; apply: lf_bijective.
        - move=> t /setI2_P [tx1] /indexed_P [pt PE Qt].
          by apply: Zo_i => //; rewrite -Qt pt.
        - move=> u v /setI2_P [_] /indexed_P [pt _ Qt] 
              /setI2_P [_] /indexed_P [pv _ Qv].
          by move=> aux; apply: pair_exten => //; ue.
        - move=> y  /Zo_P [yE px1]. 
          exists (J y C2); last by aw.
          by apply/setI2_P;split => //;apply:indexed_pi.
      exists (Lf P (x1 \cap Fi) H2).
        saw; apply: lf_bijective.
        + move=> t /setI2_P [tx1] /indexed_P [pt PE Qt].
          by apply: Zo_i => //; rewrite -Qt pt.
        + move=> u v /setI2_P [_] /indexed_P [pt _ Qt] 
            /setI2_P[_] /indexed_P  [pv _ Qv] aux.
          apply: pair_exten => //; ue.
        + move=> y =>/Zo_P [yE px1];  exists (J y C1); last by aw.
          by apply /setI2_P; split => //; apply: indexed_pi.
  have hE: sub H1 E by apply: Zo_S.
  move: (h1 _ hE); set K:= (union _).
  have KM: sub K F.
    move=> t /setU_P [y ty] /funI_P [z zH1 zh2].
    move: zH1 => /Zo_P [zE _].
    by move: (Ap _ zE); rewrite - zh2; apply.
  move: (cardinal_setC KM); rewrite -/m.
  suff: (sub H2 (F -s K)).
    move=> s1; move: (sub_smaller s1) => qa qb qc.
    by rewrite -qb; apply: csum_Mlele.
  move=> t =>/Zo_P [tF px1]; apply /setC_P;split => //.
  move=> /setU_P [y ty] /funI_P [z zH1 Az].
  move: zH1 => /Zo_P [zE J2x1].
  have le1: (gle r (J t C1) (J z C2)).
    apply /rvP;split;fprops; constructor 3; aw. 
    split => //; [ by right | by rewrite - Az].
  by move: (pr2_def (x1f _ _ px1 J2x1 le1))=> h; case:n21.
(** To each element [x] of [F] we associate the set of the partition that 
contains [x]; this is a bijection [f]; we get similarly an injection [g] on [E].
*)
have mN: inc m Nat by  move: fsF => /NatP.
move: (Exercise4_5d or mN pc) => [X [[[uX deX] neX] cX toeX]].
pose f x := choose (fun z => inc (J x C1) z /\ inc z X). 
have fp1: forall x, inc x F -> (inc (J x C1) (f x) /\ inc (f x) X).
  move=> x xF; apply choose_pr;move:(Fp1 _ xF); rewrite - sr -uX;move /setU_P.
  by move => [t t1 t2]; exists t.
have taf: lf_axiom f F X by move => t tF; move: (fp1 _ tF) => [p1 p2].
have bijF: bijection (Lf f F X).
   apply:bijective_if_same_finite_c_inj;first by rewrite lf_source lf_target cX.
     by aw.
  apply: lf_injective => //.
  move => u v uF vF;  move: (fp1 _ uF) (fp1 _ vF) => [p1 p2] [p3 p4] sf.
  rewrite - sf in p3; move /total_subordersP: (toeX _ p2) => [sfu [orf]].
  rewrite iorder_sr // => aux.
  move: (aux _ _ p1 p3); case => leuv; move: (iorder_gle1 leuv)
     => /rvP [qa qb]; case => aux1.
  + exact: (pr1_def aux1).
  + by move: aux1; aw; move=> [r1 _ _]; case: n01.
  + by move: aux1; aw; move=> [_ r1 _]; case: n21.
  + symmetry; exact (pr1_def aux1).
  + by move: aux1 => [_ _ ]; aw. 
  + by move: aux1; aw; move=> [_ r1 _]; case: n21.
pose g x := choose (fun z => inc (J x C2) z /\ inc z X).
have gp1: forall x, inc x E -> (inc (J x C2) (g x) /\ inc (g x) X).
  move=> x xE;apply choose_pr;move: (Ep1 _ xE); rewrite - sr -uX; move/setU_P.
  by move => [t t1 t2]; exists t.
have tag: lf_axiom g E X by move => t tE; move: (gp1 _ tE) => [p1 p2].
have bijG: injection (Lf g E X).
  apply: lf_injective => //.
  move => u v uF vF;  move: (gp1 _ uF) (gp1 _ vF) => [p1 p2] [p3 p4] sf.
  rewrite - sf in p3; move/total_subordersP: (toeX _ p2) => [sfu [orf]].
  rewrite iorder_sr //.
  move=> aux; move: (aux _ _ p1 p3); case => leuv; move: (iorder_gle1 leuv)
     => /rvP [qa qb]; case; aw => aux1.
  + exact: (pr1_def aux1).
  + by move: aux1 => [_ _].
  + by move: aux1 => [aux2 _ _];case: aux2=> h; [case: n20 | case: n21].
  + by rewrite (pr1_def aux1).
  + by move: aux1 => [_ _ ->].
  + by move: aux1 => [aux2 _ _];case: aux2=> h; [case: n20 | case: n21].
(** By composition, we have an injection [E->F], a solution to the problem  *)
set h := compose (inverse_fun (Lf f F X)) (Lf g E X).
have sh: source h = E by rewrite /h; aw.
have th: target h = F by rewrite /h; aw.
move: (inverse_bij_fb bijF) => bif.
have cifg: composable (inverse_fun (Lf f F X)) (Lf g E X).
  by split => //; try fct_tac; aw.
have ih: injection h by apply: compose_fi => //; move: bif => [ok _].
have ph: forall x, inc x E -> inc (Vf h x) (A x).
  move=> x xE; rewrite /h; aw.
  set y := Vf  (inverse_fun (Lf f F X)) (g x).
  have yF: inc y F.
     have ->: F = target (inverse_fun (Lf f F X)) by aw.
     by apply: Vf_target; try fct_tac;  aw; apply: tag.
  move: (fp1 _ yF) (gp1 _ xE) => [p1 p2] [p3 p4].
  have aux: inc (g x) (target  (Lf f F X)) by aw; apply: tag.
  move: (inverse_V bijF aux); rewrite -/y LfV // compfV//;  aw; bw => //.
  move=> eq0; rewrite - eq0 in p3; aw.
  move /total_subordersP: (toeX _ p2) => [sfy [orX]]; rewrite iorder_sr //.
  move=> aux1; move: (aux1 _ _ p1 p3); case => leuv; move: (iorder_gle1 leuv);
    move /rvP=> [qa qb]; case => aux2;
     try (case: n21;move: (pr2_def aux2); fprops); move: aux2; aw.
  + by move=> [zbc _]; case: n01.
  + by move=> [_ _].
  + by move=> [zba _]; case: n01.
  + by move=> [_ zbc _]; case: n21.
have gp: forall t, inc t G -> inc (J t C0) (f t). 
  move=> t tG; move: (Gp1 _ tG); rewrite - sr -uX => /setU_P [y Jy yX].
  move: (fp1 _ (GF _ tG)) => [Jf1 fX].
  set z := Vf (inverse_fun (Lf f F X)) y.
  have zF: inc z F. 
    have ->: F = target (inverse_fun (Lf f F X)) by aw.
    apply: Vf_target => //; [fct_tac | by aw ].
  have: y = Vf (Lf f F X) z by rewrite inverse_V => //; aw.
  rewrite LfV//; move: (fp1 _ zF) => [p5 p6].
  move => yf; rewrite yf in Jy.
  case: (equal_or_not z t) => zt; first by move: Jy; rewrite zt.
  move /total_subordersP: (toeX _ p6) => [aux3 [orX]]; rewrite iorder_sr //.
  move=> aux1; move: (aux1 _ _ Jy p5);case => leuv;move: (iorder_gle1 leuv);
    move /rvP => [qc qd]; case => aux2.
  + by case: zt; move: (pr2_def aux2).
  + by case: zt; move: aux2 => [_ _]; aw. 
  + by case: n21;move: aux2=> [_ e1 _]; move: e1;aw. 
  + by case: zt; move: (pr1_def aux2). 
  + by case: zt; move: aux2 => [_ _]; aw. 
  + by case: n20;move: aux2=> [_ e1 _]; move: e1;aw. 

 by exists h.

Qed.

(** We deduce that [E46b_conc]  implies [E46b_conc] *)

Lemma Exercise4_6l E F A:
  finite_set F -> (forall x, inc x E -> sub (A x) F) ->
   E46b_conc E A ->  E46b_hyp E F A.
Proof.
move=> pa pb pc.
apply: (Exercise4_6k  (G := emptyset)) => //; first fprops.
move=> L LE.
have ->: L =emptyset.
   apply /set0_P; move=> y yL; case: (LE _ yL); case.
rewrite cardinal_set0.
apply: cle0x; fprops.
Qed.

(** TODO: show that [E46c_hyp G] holds. But we do not know what to do with 
assumption  [E46c_conc G] *)


(** ---- Exercise 4.7. In a lattice [E], an element is said to be irreducible
if it is never a strict supremum. 

Let [J] be the set of irreducible elements; [P] the set [J] minus the least 
element (if it exists);  [S(x)] be the set of irreducible
elements that are [ <= x]. We start with some auxiliary results. In particular,
in a distributive lattice, if [a] is irreducible and [a <= sup(x,y)] then 
[a<=x] or [a<=y]. *)

Lemma char_fun_sub A A' B:  sub A B -> sub A' B ->
  ((sub A A') <-> (forall x, inc x B -> 
     (Vf (char_fun A B) x) <=c (Vf (char_fun A' B) x))).
Proof.
move=> AB A'B; split.
  move => AA' x xB; case: (inc_or_not x A) => xA. 
    rewrite char_fun_V_a // char_fun_V_a //;[ fprops | by apply: AA'].
  rewrite char_fun_V_b //; last by apply /setC_P.
  by apply: cle0x; apply: char_fun_V_cardinal.
move=> h t tA;  ex_middle ta'; move: (AB _ tA) => tB.
move: (h _ tB); rewrite  char_fun_V_a // char_fun_V_b //; last by apply /setC_P.
by move /(cltNge clt_01).
Qed.

Definition sup_irred r x:= 
  forall a b, inc a (substrate r) -> inc b (substrate r) ->
   x = sup r a b -> (x = a \/ x = b).

Definition irreds r := Zo (substrate r)(sup_irred r).

Definition E47S r x := Zo (substrate r) 
   (fun z => (sup_irred r z) /\ (gle r z x)).


Section Irred_lattice.

Variable r:Set.
Hypothesis lr:lattice r.

Lemma Exercise4_7a x: inc x (substrate r) ->
 sup_irred r x \/ (exists a b, [/\ glt r a x, glt r b x & x = sup r a b]).
Proof.
case: (p_or_not_p (sup_irred r x)); first by left.
move=> p1; right; ex_middle h; case: p1 => a b asr bsr xs.
case: (equal_or_not x a)=> xa; first by left.
case: (equal_or_not x b)=> xb; first by right.
move: (lattice_sup_pr lr asr bsr); rewrite -xs; move => [p2 p3 _].
by case: h; exists  a, b; rewrite /glt;split => //;split => //; apply: nesym.
Qed.

Lemma Exercise4_8a a: distributive_lattice3 r -> 
  sup_irred r a ->
  forall x y, inc x (substrate r) -> inc y (substrate r) ->
   gle r a (sup r x y) -> (gle r a x \/ gle r a y).
Proof.
move => dl1 sia x y xsr ysr sa.
have or: order r by move: lr => [or _].
have asr: inc a (substrate r) by order_tac.
move:(distributive_lattice_prop2 lr) => [_  _ p1]. 
move: ((p1 dl1) _ _ _ asr xsr ysr); rewrite (inf_comparable1 or sa) => ia. 
move: (lattice_inf_pr lr asr xsr)(lattice_inf_pr lr asr ysr).
move=> [_ px _] [_ py _].
have r1: inc (inf r a x) (substrate r) by order_tac.
have r2: inc (inf r a y) (substrate r) by order_tac.
by case: (sia _ _ r1 r2 ia); move=> ->; [left | right].
Qed.

(** If [E] is finite, any non-empty set has a minimal and a maximal element.
   In particular, [E] has a least element, which is irreducible.
Any finite set has a supremum and an infimum. The supremum of [S(x)] is [x].
We restate this: any [x] is the supremum of a finite number of irreducible
elements.
  *)

Hypothesis fs: finite_set (substrate r).
Hypothesis nes: nonempty (substrate r).

Definition E48P := (irreds r) -s1 (the_least r).

Lemma Exercise4_7b: order r.
Proof. by move: lr => [or _].  Qed.

Lemma finite_set_maximal1 U: sub U (substrate r) -> nonempty U ->
  exists2 x, inc x U & (forall y, inc y U -> gle r x y -> x = y).
Proof.
move: Exercise4_7b=> or  Usr neU.
set r':= induced_order r U.
move: (iorder_osr or Usr) => [or' sr'].
move:(sub_finite_set Usr fs); rewrite - sr' => fsE.
rewrite - sr' in neU.
move: (finite_set_maximal or' fsE neU) => [x [xs xm]].
ex_tac; move=> y yser' xy; symmetry; apply: xm; apply /iorder_gle0P => //; ue.
Qed.

Lemma finite_set_minimal1 U: sub U (substrate r) -> nonempty U ->
  exists2 x, inc x U & (forall y, inc y U -> gle r y x -> y = x).
Proof.
move: Exercise4_7b => or  Usr neU.
set r':= opp_order (induced_order r U).
move: (iorder_osr or Usr) => [or1 sr1].
move: (opp_osr or1) => [or']; rewrite sr1 => sr'.
move:(sub_finite_set Usr fs); rewrite - sr' => fsE.
rewrite - sr' in neU.
move: (finite_set_maximal or' fsE neU) => [x [xs xm]].
ex_tac; move=> y yser' xy; apply: xm; apply /opp_gleP.
apply /iorder_gle0P => //; ue.
Qed.

Lemma Exercise4_7c: has_least r.
Proof. 
move: (finite_set_minimal1 (@sub_refl (substrate r)) nes).
move=> [x xsr xp]; exists x;split => // u usr.
move: (lattice_inf_pr lr xsr usr)=> [p1 p2 p3].
move: lr => [or _].
have isr:inc (inf r x u) (substrate r) by order_tac.
by move: (xp _ isr p1) => aux; rewrite aux in p2.
Qed.

Lemma Exercise4_7d: inc (the_least r) (irreds r).
Proof.
move: Exercise4_7b Exercise4_7c => or el.
move: (the_least_pr or el) => [p1 p2].
apply: (Zo_i p1); case: (Exercise4_7a p1) => //- [a [_ [al _ _]]].
have asr: inc a (substrate r) by order_tac.
move: (p2 _ asr) => p3; order_tac.
Qed.

Lemma Exercise4_7e: sub E48P (substrate r).
Proof.
apply: (@sub_trans  (irreds r));[ apply: sub_setC | apply: Zo_S].
Qed.

Lemma Exercise4_7f:  
  irreds r = E48P +s1 (the_least r).
Proof. rewrite  setC1_K //; apply: Exercise4_7d. Qed.

Lemma Exercise4_7g a:  inc a (substrate r) ->
  inc (the_least r) (E47S r a).
Proof.
move: Exercise4_7b=> or  asr.
move: (the_least_pr or (Exercise4_7c)) => [p1 p2].
apply: Zo_i => //;split;fprops.
by move: Exercise4_7d => /Zo_P [].
Qed.

Lemma Exercise4_7h a: inc a (substrate r) -> nonempty  (E47S r a).
Proof. by exists (the_least r); apply: Exercise4_7g. Qed.

Lemma Exercise4_7i x: sub x (substrate r) ->
  has_supremum r x.
Proof.
move: Exercise4_7b => or xr; case: (emptyset_dichot x) => nex.
  move: (the_least_pr or  Exercise4_7c) => tlp.
  rewrite nex; exists (the_least r).
  rewrite lub_set0 //.
apply:  (lattice_finite_sup2 lr (sub_finite_set xr fs) nex xr). 
Qed.

Lemma Exercise4_7j a: inc a (substrate r) ->
  gle r (supremum r (E47S r a)) a.
Proof.
move => asr; move: (Exercise4_7h asr) => ne.
have sE: sub (E47S r a) (substrate r) by apply: Zo_S.
apply /(lattice_finite_sup3P lr  _ (sub_finite_set sE fs) ne sE).
by move=> z /Zo_hi [].
Qed.

Lemma Exercise4_7k a b:
  gle r a b -> sub (E47S r a)  (E47S r b).
Proof.
move: Exercise4_7b=> or ab t.
move /Zo_P => [p1 [p2 p3]]; apply /Zo_P; split => //; split => //;order_tac.
Qed. 

Lemma Exercise4_7l u: inc u (substrate r) ->
  (supremum r (E47S r u)) = u.
Proof.
move: Exercise4_7b => or  usr.
apply: (order_antisymmetry or); first by apply: Exercise4_7j.
ex_middle bad.
set U := Zo (substrate r) (fun z => ~ gle r z (supremum r (E47S r z))).
have neU:nonempty U by exists u; apply: Zo_i.
have su: sub U (substrate r) by apply: Zo_S.
move: (finite_set_minimal1 su neU) => [t tu tv].
move: (tu) => /Zo_P [tsr bad1]; case: bad1.
have sV: sub (E47S r t) (substrate r) by apply: Zo_S.
move: (Exercise4_7i sV) => hst.
move: (supremum_pr or sV hst) => [[ub1 ub2] _].
case: (Exercise4_7a (su _ tu)) => aux.
   have h: inc t (E47S r t) by apply: Zo_i => //;split => //; order_tac.
   by apply: ub2.
move: aux => [a [b [[leat neat] [lebt nebt ts]]]].
case: (p_or_not_p (gle r a (supremum r (E47S r a)))); last first.
  move=> p1;case: neat; apply: tv => //; apply: Zo_i => //; order_tac.
case: (p_or_not_p (gle r b (supremum r (E47S r b)))); last first.
  move=> p1;case: nebt; apply: tv => //; apply: Zo_i => //; order_tac.
move=> bs1 bs2.
have asr: inc a (substrate r) by order_tac.
have bsr: inc b (substrate r) by order_tac.
have s1:= (Exercise4_7k leat).
have s2:=(Exercise4_7k lebt).
have hs1:=(Exercise4_7i (sub_trans s1 sV)).
have hs2:=(Exercise4_7i (sub_trans s2 sV)).
have le2:=(sup_increasing or (sub_trans s1 sV) sV s1 hs1 hst).
have le1:=(sup_increasing or (sub_trans s2 sV) sV s2 hs2 hst).
move: (lattice_sup_pr lr asr bsr); rewrite -ts; move=> [h1 h2 h3].
apply: h3; order_tac.
Qed.

(** The function [S] is an order isomorphism [E -> X] for some subset [X] of the
powerset of [E] order by inclusion.
[S] of inf is intersection of [S] *)

Lemma Exercise4_7m a b:
  inc a (substrate r) -> inc b (substrate r) ->
  sub (E47S r a)  (E47S r b) -> gle r a b.
Proof.
move => asr bsr sab.
set E := (E47S r a).
have sE: sub E (substrate r) by apply: Zo_S.
move: (sub_finite_set sE fs) => fsE.
rewrite - (Exercise4_7l asr).
apply /(lattice_finite_sup3P lr _ fsE (Exercise4_7h asr) sE).
by move=> z zE; move: (sab _ zE) =>/Zo_hi [_].
Qed.

Lemma Exercise4_7n a: inc a (substrate r) ->
  exists S, [/\ finite_set S, nonempty S, sub S (substrate r),
  (forall x, inc x S -> sup_irred r x) &
  supremum r S = a].
Proof. 
move=> asr.
have sE: sub (E47S r a) (substrate r) by apply: Zo_S.
move: (sub_finite_set sE fs) => fsE.
move: (Exercise4_7h asr)  (Exercise4_7l asr) => ne ass.
by exists (E47S r a);split => // x /Zo_hi [].
Qed.

Lemma Exercise4_7o a b: inc a (substrate r) -> inc b (substrate r) ->
  (E47S r (inf r a b)) = (E47S r a) \cap (E47S r b).
Proof.
move=> asr bsr.
move: (lattice_inf_pr lr asr bsr)=> [p1 p2 p3].
have isr: inc (inf r a b) (substrate r) by order_tac.
move: (Exercise4_7k p1) (Exercise4_7k p2) => p4 p5.
set_extens t; first by move=> t1; apply /setI2_P; split; fprops.
move => /setI2_P [] /Zo_P [tsr [si ta]] /Zo_hi [_ tb]; apply /Zo_P;split;fprops.
Qed.

Lemma Exercise4_7p:
  let tg := (irreds r) in 
   order_morphism (Lf (E47S r) (substrate r) (\Po tg))
   r (subp_order tg).
Proof.
move: lr => [or _] tg.
have ta: forall x, inc x (substrate r) -> inc (E47S r x) (\Po tg).
  by move=> x xsr; apply /setP_P => t /Zo_P [p1 [p2 p3]]; apply /Zo_P.
move: (subp_osr tg) => [pa pb].
split; fprops; rewrite ? pb;first by saw; apply: lf_function.
hnf; aw;move=> x y xsr ysr; hnf;rewrite !LfV//; split.
   move => pa1; apply /sub_gleP;split;fprops.
   by apply: Exercise4_7k.
by move /sub_gleP => [pa1 [pb1 pc]]; apply:Exercise4_7m.
Qed.

Lemma Exercise4_7q a: inc a (substrate r) 
 -> sub (E47S r a) (irreds r).
Proof. by move=> asr b => /Zo_P [pa [pb pc]]; apply /Zo_P. Qed.

(** ---- Exercise 4.8. We assume that [E] is a distributive lattice.

We have: [S] of sup is union of [S].
If [t] is irreducible, [U] a non-empty set of irhnfucibles, [t<= sup U] simplies
that [t <= x] for at least one element of [U]. Let [p(U)] be the property
that [U] is a non-empty set of irreducibles, such that [x <=y],  [x] irrefucible
and [y] in [U] implies [x] in [U]. Then [U = S(sup U)]. Moreover [p (S(x))]
holds for any [x]. *)

Hypothesis dl3: distributive_lattice3 r.

Lemma Exercise4_8b a b: inc a (substrate r) -> inc b (substrate r) ->
  (E47S r (sup r a b)) = (E47S r a) \cup (E47S r b).
Proof.
move=> asr bsr.
move: (lattice_sup_pr lr asr bsr)=> [p1 p2 p3].
have isr: inc (sup r a b) (substrate r) by order_tac.
have or: order r by move: lr => [ok _]. 
move: (Exercise4_7k p1) (Exercise4_7k p2) => p4 p5.
set_extens t; last first.
  case /setU2_P => /Zo_P  [tsr [si ta]];
       apply /Zo_P;split => //; split => //; order_tac.
move /Zo_P=> [tsr [si ts]].
by case: (Exercise4_8a dl3 si asr bsr ts)=> le;
 apply /setU2_P;[left | right]; apply: Zo_i. 
Qed.


Lemma Exercise4_8c1 t U: inc t (substrate r) ->
  sup_irred r t ->  sub U (irreds r) ->  gle r t (supremum r U) ->
  nonempty U ->  exists2 x, inc x U & gle r t x.
Proof.
move: Exercise4_7b => or  tsr sit Usi tsU neU.
pose pA U := sub U (irreds r) /\ gle r t (supremum r U).
pose pB U := exists2 x, inc x U & gle r t x.
have sis: sub (irreds r) (substrate r) by apply: Zo_S.
have Usr: sub U (substrate r) by apply: (@sub_trans  (irreds r)). 
move: (sub_finite_set Usr fs) => fsU.
apply: (@finite_set_induction2 pA pB) => //. 
  move => a; rewrite /pA /pB; move=> [p1 p2].
  have :inc a (irreds r) by apply: p1; fprops.
  move /Zo_P=> [asr ai];  move: p2.
  rewrite supremum_singleton // => ta; exists a;fprops.
move => a b aux nea; rewrite /pA /pB; move=> [p1 p2].
have air: sub a (irreds r). 
  apply: (@sub_trans  (a +s1 b))  => //; fprops.
have bir: inc b (irreds r) by apply: p1; fprops.
have asr: sub a (substrate r) by apply: (@sub_trans  (irreds r)).
have bsr: inc b (substrate r) by apply: sis.
have fsa := (sub_finite_set asr fs).
have hsa: has_supremum r a by apply: lattice_finite_sup2 => //.
move: p2; rewrite supremum_setU1 // => aux2.
move: (supremum_pr1 or hsa) => /(lubP or asr) [[p2 p3] p4].
case: (Exercise4_8a dl3 sit p2 bsr aux2)=> aux3; last by exists b; fprops.
have aux4: pA a by split.
move: (aux nea aux4)=> [x xa tx]; exists x;fprops.
Qed.

Lemma Exercise4_8c U: sub U (irreds r) ->
   (forall x y, inc y U -> sup_irred r x -> gle r x y -> inc x U) ->
   nonempty U ->
  U = (E47S r (supremum r U)).
Proof.
move: Exercise4_7b => or Usi hU neU.
have sis: sub (irreds r) (substrate r) by apply: Zo_S.
have Usr: sub U (substrate r) by apply: (@sub_trans  (irreds r)). 
have fsU:= (sub_finite_set Usr fs).
have hs := (lattice_finite_sup2 lr fsU neU Usr).
move: (supremum_pr or Usr hs) => [[ub1 ub2] ub3].
set_extens t => ts.
  move: (ub2 _ ts) (Usi _ ts) => aux /Zo_P [p1 p2]. 
  by apply /Zo_P;split => //; apply: Usr. 
move: ts => /Zo_P [tsr [srt ltsr]].
move: (Exercise4_8c1 tsr srt Usi ltsr neU) => [x sU tx].
exact: (hU _ _ sU srt tx).
Qed.


Lemma Exercise4_8d: 
  let p:= fun U => [/\ sub U (irreds r), nonempty U &
    (forall x y, inc y U -> sup_irred r x -> gle r x y -> inc x U)] in
  (forall x, inc x (substrate r) -> p (E47S r x)) /\
  (forall U, p U -> exists2 x, (inc x (substrate r)) & U = (E47S r x)).
Proof.
move: Exercise4_7b=> or p; split.
  move=> x xsr; split => //.
      by move=> t  /Zo_P [pa [pb pc]]; apply /Zo_P. 
    by apply: Exercise4_7h.
  move=> u v /Zo_P [vsr [su vx]] iu uv. 
  apply /Zo_P; split => //; try split => //;order_tac. 
move=> U [p1 p2 p3]; rewrite (Exercise4_8c p1 p3 p2).
exists  (supremum r U) => //.
have sU: sub U (substrate r).
  by move=> t tu; move: (p1 _ tu) => /Zo_P [].
by move: (supremum_pr1 or (Exercise4_7i sU)) => /(lubP or sU) [[ok _] _].
Qed.


(** Let [Sb(x)] be [S(x)] without the least element of [E]. These two sets have
the same supremum. The previous result can be rewriten as
Let [q(U)] be the property that [U] is a subset of [P] such that [x <=y],
[x] irreducible and [y] in [U] implies [x] in [U]. Then [Sb(x)] satisfies [q] 
and any set satisfying [q] has the form [Sb(x)].*)

Lemma Exercise4_8e: 
  let comp:= fun X => X -s1 (the_least r) in 
  let p:= fun U => (sub U E48P /\
    (forall x y, inc y U -> inc x E48P -> gle r x y -> inc x U)) in
  (forall x, inc x (substrate r) -> p (comp (E47S r x))) /\
  (forall U, p U -> exists2 x, (inc x (substrate r)) & U = comp (E47S r x)).
Proof.
move: Exercise4_7b  Exercise4_8d => or [pa pb] comp p; split.
  move=> x xsr; move: (pa _ xsr) => [p1 p2 p3]; split.
    move => t /setC1_P [p4 p5]; apply /setC1_P;split;fprops.
  move=> z y /setC1_P [yE yne] /setC1_P [zi znl] zy;apply/setC1_P;split=> //.
  move: zi => /Zo_P [_ zi]; apply: (p3 _ _ yE zi zy).
move=> U [p1 p2].
set U' := U +s1 (the_least r).
have [x xsr aux]:exists2 x, inc x (substrate r) & U' = E47S r x.
  apply: (pb U'); split => //.
      move=> t; case /setU1_P; last by move => ->; apply: Exercise4_7d.
      by move=> tu; move: (p1 _ tu) => /setC1_P [].
    by exists  (the_least r);  rewrite /U';fprops.
  move=> x y yU' ir xy; apply /setU1_P.
  have xsr: inc x (substrate r) by order_tac.
  case: (equal_or_not x (the_least r)) ; [ by right | move => nxle; left].
  have xp: inc x E48P by apply /setC1_P;split => //; apply: Zo_i.
  move: yU' => /setU1_P; case.
    by move=> yU; move: (p2 _ _ yU xp xy).
    move: (the_least_pr or  Exercise4_7c) => [_ tle].
  move=> h; rewrite h in xy; case: nxle; move: (tle _  xsr) => aux; order_tac.
ex_tac. 
rewrite -aux; set_extens t. 
   move => tu; apply /setC1_P; split => //; first by apply /setU1_P; left.
   by move: (p1 _ tu) => /setC1_P [].
move /setC1_P => [] /setU1_P; case => //.
Qed.

(** Let's consider the sets [FJ] and [FP] of increasing functions [J->d] 
and [P->d], respectively,  where the first set is [J] or [P],
ordered by the opposite ordering, and the second set is 
the doubleton [(0,1)] ordered by [0<1]. These are ordered sets. 
To each [x] we associate the characteristic function of [S(x)] and [Sb(x)].
This give an order isomorphism from [E] onto a subset of [FJ] and [FP], because
the conditions [p] and [q] considered above just say that the characteristic
function is increasing.

Bourbaki says that the first mapping is bijective. This is wrong, because the 
constant function zero is never the characteristice function of [S(x)].
We get a bijection be excluding this function. On the other hand the second
mapping is bijective.
*)

Definition E48I := doubleton \0c \1c.
Definition E48z := Lf (fun z => \0c) (irreds r) E48I.
Definition E48Ps := opp_order (induced_order r E48P).
Definition E48Js := opp_order (induced_order r (irreds r)).
Definition E48Io :=  Nint_cco \0c \1c.
Definition E48AJIo := increasing_mappings_order E48Js E48Io.
Definition E48APIo := increasing_mappings_order E48Ps E48Io.
Definition E48AJI := increasing_mappings E48Js E48Io.
Definition E48API := increasing_mappings E48Ps E48Io.
Definition E48AJImo:=  
  induced_order E48AJIo ((substrate E48AJIo) -s1 E48z).

Lemma Exercise4_8f K: sub K (substrate r) ->
   order_on (opp_order (induced_order r K)) K.
Proof.
move: Exercise4_7b => or Ksr.
move: (iorder_osr or Ksr) => [or1 {2} <-]; exact: (opp_osr or1).
Qed.

Lemma Exercise4_8g: 
  order_on E48Js (irreds r) /\ order_on E48Ps E48P.
Proof.
have s1: sub (irreds r) (substrate r) by apply: Zo_S.
by move: (Exercise4_8f s1)  (Exercise4_8f Exercise4_7e) => [p1 p2][p3 p4]. 
Qed.

Lemma Exercise4_8h: order_on E48Io E48I.
Proof.
hnf;move: (Ninto_wor \0c \1c)=> [[ok _] ->].
split => //;set_extens t.
  move /(NintcP NS1) => t1.
  case: (equal_or_not t \1c) => to; first by  apply /set2_P; right.
  by move /clt1: (conj t1 to) => -> ; apply /set2_P; left.
case /set2_P => ->; apply /(NintcP NS1); fprops; apply:cle_01.
Qed.

Lemma Exercise4_8iP K
   (o :=  opp_order (induced_order r K))
   (A:= increasing_mappings o E48Io):
  sub K (substrate r) ->
 forall f, inc f A <->
  [/\ function f, source f = K, target f =  E48I &
  (forall i j, inc i K -> inc j K -> gle r i j -> 
     Vf f j = \1c -> Vf f i = \1c)].
Proof.
move=> Ksr f.
move: Exercise4_8h (Exercise4_8f Ksr) => [o1 s1] [o2 s2].
have oi: order r by move: lr => [or _].
move: (iorder_osr oi Ksr) => [o0 s0].
split.
  move /soimP => [[ff sf tf] incf]; split => //; try ue.
  move => i j isr jsr ij f1.
  move:incf => [p1 p2 [p3 p4 p5] p6].
  have aux: gle o j i by apply /opp_gleP/iorder_gleP;split => //.
  move: (p6 _ _ aux); rewrite f1;move /Ninto_gleP => [_] /(NintcP NS1). 
  apply: cleA.
move=> [ff sf tf incf].
have aux: function_prop f (substrate o) (substrate E48Io) by split => //; ue.
apply /soimP; split => //; split => //.
move => x y / opp_gleP /iorder_gleP [xk yk yx].
have wx: inc (Vf f x) (target f) by Wtac.
have wy: inc (Vf f y) (target f) by Wtac.
move: s1; rewrite (proj2 (Ninto_wor \0c \1c)) => ww.
rewrite tf in wx wy;apply /(Ninto_gleP); rewrite ww;split => //.
move: (incf _ _ xk yk yx).
case /set2_P: wx => -> ; case /set2_P: wy => ->; fprops => h; try apply:cle_01.
by  move: (h (erefl \1c)) => ->; fprops.
Qed.

Lemma Exercise4_8j K
  (o :=  opp_order (induced_order r K))
  (A:= increasing_mappings o E48Io)
  (no := increasing_mappings_order o E48Io):
  sub K (substrate r) ->order_on no A.
Proof.
move=> Ksr; move: (Exercise4_8f Ksr) Exercise4_8h => [p1 p2] [p3 p4].
by apply: imo_osr.
Qed.

Lemma Exercise4_8k:
  order_on E48AJIo E48AJI /\ order_on E48APIo E48API.
Proof.
have s1: sub (irreds r) (substrate r) by apply: Zo_S.
by move: (Exercise4_8j s1)  (Exercise4_8j Exercise4_7e) => [p1 p2][p3 p4].
Qed.

Lemma Exercise4_8l: inc E48z (substrate E48AJIo).
Proof.
move:  Exercise4_8k => [[_ p1] _ ]; rewrite p1.
have s1: sub (irreds r) (substrate r) by apply: Zo_S.
have ta: lf_axiom (fun _ : Set => \0c) (irreds r) E48I.  
   rewrite /E48I;move=> t _; fprops.
apply /(Exercise4_8iP s1); rewrite /E48z; saw.
  by apply: lf_function.
move => i  j ii ji; rewrite !LfV//.
Qed.

Lemma Exercise4_8m:
 order_on E48AJImo (E48AJI -s1 E48z)  /\
 forall f, inc f (substrate E48AJImo) <->
    (inc f E48AJI /\ Vf f (the_least r) = \1c).
Proof.
move:  Exercise4_8k Exercise4_8l => [[p1 p2] _] p3.
have p4:sub (E48AJI -s1 E48z) E48AJI by apply: sub_setC.
move: p4; rewrite -p2 => p5.
have p6:substrate E48AJImo = E48AJI -s1 E48z.
  rewrite /E48AJImo iorder_sr//; ue.
split; first by apply:(iorder_osr p1 p5).
move: Exercise4_7d => lj.
have ta:lf_axiom (fun _ : Set => \0c) (irreds r) E48I.
  rewrite /E48I => t _; fprops.
rewrite p6 p2=> f; split; last first.
  move=> [p7 p8];apply /setC1_P; split => //.
  move=> sf; rewrite sf in p8; move: p8; rewrite /E48z LfV//; fprops.
move /setC1_P => [p7 p8];split => //.
have s1: sub (irreds r) (substrate r) by apply: Zo_S.
move: p7 => /(Exercise4_8iP s1) [ff sf tf icf].
move: (lj); rewrite - sf => lj1.
move: (Vf_target ff lj1);rewrite tf; case /set2_P => // wlp.
case: p8; rewrite /E48z;apply: function_exten;aw; trivial.
  by apply: lf_function.
move=> x xsf; move: (xsf); rewrite sf => xsr; rewrite LfV //.
move: (Vf_target ff xsf);rewrite tf; case /set2_P => // wo.
move: lr => [or _].
move: (the_least_pr or  Exercise4_7c) => [_ tle].
move: (icf _ _ lj xsr (tle _ (s1 _ xsr)) wo).
by rewrite wlp; move=> ->.
Qed.

Lemma  Exercise4_8n x: inc x (substrate r) ->
  inc (char_fun (E47S r x) (irreds r)) (substrate E48AJImo).
Proof.
have s1: sub (irreds r) (substrate r) by apply: Zo_S.
move => xsr.
move: (Exercise4_7q xsr) (Exercise4_7g xsr) => q0 q1.
move: Exercise4_8m => [[p1 p2] p3]; rewrite p3.
split; last by rewrite char_fun_V_a //.
apply /(Exercise4_8iP s1); rewrite /char_fun; saw.
    apply: char_fun_f.
move=> i j isr jsr ij; rewrite !LfV//; try apply: char_fun_axioms.
rewrite /varianti.
Ytac jE; last by move=> zo; case: card1_nz.
move=> _; Ytac iE => //; case: iE. 
move: jE isr => /Zo_hi  [_ jx] /Zo_P [pa pb]; apply /Zo_P;split => //.
move: lr => [or _];split => //; order_tac.
Qed.

Lemma Exercise4_8o x (comp:= fun X => X -s1 (the_least r)):
  inc x (substrate r) ->
  inc (char_fun (comp (E47S r x)) E48P) E48API.
Proof.
move: (Exercise4_7e) => s1 xsr. 
apply /(Exercise4_8iP s1); rewrite  /char_fun;saw.
    apply: char_fun_f.
move=> i j isr jsr ij; rewrite !LfV//; try apply: char_fun_axioms.
rewrite /varianti;Ytac jE; last by move=> zo; case: card1_nz.
move=> _; Ytac iE => //; case: iE. 
move:jE isr => /setC1_P [] /Zo_hi [_ jx] njl /Zo_P []/Zo_P [pa pb]/set1_P nil.
apply /setC1_P;split => //; apply /Zo_P;split => //; split => //. 
move: lr => [or _];order_tac.
Qed.

Lemma Exercise4_8p f: function f -> target f = E48I ->
   char_fun (Vfi1 f \1c) (source f) = f.
Proof. 
move=> ff tf;rewrite /char_fun; apply: function_exten; aw; trivial.
  apply: char_fun_f.
  by rewrite tf.
move=> x xs; rewrite /Vfi1 LfV//; last by apply: char_fun_axioms.
move: (Vf_target ff xs); rewrite tf; case /set2_P => wf.
  rewrite /varianti Y_false //; move /iim_graph_P => [u] /set1_P -> h.
  move: (Vf_pr ff h); rewrite wf; fprops.
rewrite /varianti Y_true //; apply /iim_graph_P; exists \1c; fprops.
by rewrite -wf; apply: Vf_pr3.
Qed.

Lemma Exercise4_8qP X Y Z:  sub X Z -> sub Y Z ->
  ((sub X Y) <-> (forall x, inc x Z -> 
    gle E48Io (Vf (char_fun X Z) x) (Vf (char_fun Y Z) x))).
Proof.
move => XZ YZ; split.
   move => XY x xZ.
  apply / (Ninto_gleP2 NS0 NS1).
  case: (inc_or_not x X) => xX.
    rewrite (char_fun_V_a XZ xX)  (char_fun_V_a YZ (XY _ xX)); split; fprops.
  have xc: inc x (Z -s X) by apply /setC_P.
  rewrite (char_fun_V_b XZ xc).
  case: (inc_or_not x Y) => xY. 
    rewrite (char_fun_V_a YZ xY);split;fprops; apply:cle_01.
  have xc1: inc x (Z -s Y) by apply /setC_P.
  rewrite (char_fun_V_b YZ xc1); split;fprops; apply:cle_01.
move=> h t tx; move: (h  _ (XZ _ tx)).
rewrite /E48Io; move /(Ninto_gleP) => [_ _ aux]; ex_middle ty.
have tc: inc t (Z -s Y) by  apply /setC_P;split => //; apply: XZ.
move: aux; rewrite (char_fun_V_a XZ tx)  (char_fun_V_b YZ tc).
by move/(cltNge clt_01). 
Qed.

Lemma Exercise4_8r: r \Is E48APIo.
Proof.
pose comp X:= X -s1 (the_least r).
pose chrf x := char_fun (comp (E47S r x)) E48P.
have ta: lf_axiom chrf  (substrate r) E48API.
 by  move=> x xsr;apply: Exercise4_8o.
exists (Lf chrf (substrate r) E48API).
move: lr => [or _]; move: Exercise4_8k => [_ [p1 p2]].
have chrp: forall u, inc u (substrate r) -> sub (comp (E47S r u))  E48P.
  move=> u usr; move: (Exercise4_7q usr) => aux t /setC1_P [q1 q2] => //. 
  by apply /setC1_P;split => //; apply: aux.
saw.
  split; aw => //; apply: lf_bijective => //.
    move => u v usr vsr.
    move /(char_fun_injectiveP (chrp _ usr) (chrp _ vsr))=> scf.
    move: (Exercise4_7g usr)(Exercise4_7g vsr) => leu lev.
    move: (setC1_K leu).
    rewrite -/(comp (E47S r u)) scf /comp (setC1_K lev) => scf1.
    move: (f_equal (supremum r) scf1); rewrite Exercise4_7l // Exercise4_7l //.
   move:Exercise4_8e  => [_ p3].
  move=> y yf; set U := Vfi1 y \1c.
  move: yf => /(Exercise4_8iP (Exercise4_7e)) [fy sy ty yp].
  have p4: sub U E48P.
    rewrite - sy /U; apply: sub_inv_im_source => //; rewrite ty.
    rewrite /E48I;apply: set1_sub; fprops.
  have p5: (sub U E48P /\ 
      (forall x y, inc y U -> inc x E48P -> gle r x y -> inc x U)).
    split => // x z zU xE xz.
    move: zU  => /iim_fun_P [u /set1_P ->] Jg; move: (Vf_pr fy Jg). 
    move: (p1graph_source fy Jg); rewrite sy => zy wv.
    apply /iim_fun_P; exists \1c; first by fprops.
    symmetry in wv; rewrite - (yp _ _ xE zy xz wv); apply: Vf_pr3 => //; ue.
  move: (p3 _ p5) => [x xsr aux]; ex_tac.
  by rewrite /chrf /comp -aux /U - sy Exercise4_8p.
hnf; aw;move=> x y xsr ysr; rewrite !LfV//.
move: Exercise4_8g Exercise4_8h => [[q1 q2] [q3 q4]] [q5 q6].
have chrf1: forall x, inc x (substrate r) ->
  [/\ function (chrf x), source (chrf x) = substrate E48Ps &
   target (chrf x) = substrate E48Io].
  move => z zsr; split; first (by apply: char_fun_f). 
    by rewrite /chrf /char_fun; aw.
    rewrite /chrf /char_fun; aw; rewrite  q6 //. 
split.
move => h; move: (Exercise4_7k h) => h1.
  move: (chrf1 _ xsr)(chrf1 _ ysr) => [q7 q8 q9] [q10 q11 q12].
  have aux: (sub (comp (E47S r x)) (comp (E47S r y))).
    by move => t /setC1_P [t1 t2]; apply /setC1_P;split => //; apply: h1.
  move /(Exercise4_8qP  (chrp _ xsr)  (chrp _ ysr)): aux => hh.
  by apply /imo_gleP; fprops; split => //; fprops; split => //; rewrite q4.
move => h; apply : (Exercise4_7m xsr ysr).
move /(imo_gleP _ q5) :h => [_ _ [_ _]]. 
rewrite q4 => /(Exercise4_8qP  (chrp _ xsr)  (chrp _ ysr)).
move=> aux t t1; case: (equal_or_not t (the_least r)) => tl.
  by rewrite tl; apply: Exercise4_7g.
have t2: inc t  (comp (E47S r x)) by apply /setC1_P.
by move: (aux _ t2) => /setC1_P [].
Qed.

Lemma Exercise4_8s: r \Is E48AJImo.
Proof.
pose chrf x := char_fun (E47S r x) (irreds r).
have ta: lf_axiom chrf (substrate r) (substrate E48AJImo).
  by  move=> x xsr;apply: Exercise4_8n.
exists (Lf chrf (substrate r) (substrate E48AJImo)).
move: lr => [or _]; move: Exercise4_8k => [[p1 p2] _].
move: Exercise4_8m => [[p3 p4] p5].
have s1: sub (irreds r) (substrate r) by apply: Zo_S.
saw.
   saw; apply: lf_bijective => //.
    move => u v usr vsr.
    move /(char_fun_injectiveP (Exercise4_7q usr) (Exercise4_7q vsr))=> scf.
    move: (f_equal (supremum r) scf); rewrite Exercise4_7l // Exercise4_7l //.
  move:Exercise4_8d  => [_ p6].
  move=> y yf; set U := Vfi1 y \1c.
  move: yf; rewrite p5; move => [aux Wl]; move: aux.
  move /(Exercise4_8iP s1) => [fy sy ty yp]. 
  have p7: sub U (irreds r).
    rewrite - sy /U; apply: sub_inv_im_source => //; rewrite ty.
    rewrite /E48I;apply: set1_sub; fprops.
  have p8: nonempty U.
    exists (the_least r); apply /iim_fun_P.
    exists \1c; [ fprops | rewrite -Wl; apply: Vf_pr3 => // ].
    by rewrite sy;apply: Exercise4_7d.
  have p9: [/\ sub U  (irreds r), nonempty U &
      (forall x y, inc y U -> sup_irred r x -> gle r x y -> inc x U)].
    split => //; move=> x z zU xE xz.
    move: zU => /iim_fun_P [u /set1_P ->] Jg; move: (Vf_pr fy Jg). 
    move: (p1graph_source fy Jg); rewrite sy => zy wv.
    apply /iim_fun_P;exists \1c; first by fprops.
    have xE1: inc x (irreds r) by apply: Zo_i => //; order_tac.
    symmetry in wv;rewrite - (yp _ _ xE1 zy xz wv); apply: Vf_pr3 => //; ue.
  move: (p6 _ p9) => [x xsr aux]; ex_tac.
  by rewrite /chrf  -aux /U - sy Exercise4_8p.
hnf; aw;move=> x y xsr ysr; rewrite !LfV//; rewrite -/(chrf x) -/ (chrf y).
move: Exercise4_8g Exercise4_8h => [[q1 q2] [q3 q4]] [q5 q6].
move: (ta _ xsr) (ta _ ysr); rewrite p5 p5; move=> [p6 p7] [p8 p9].
have ta1: lf_axiom (fun _ : Set => \0c) (irreds r) E48I.
  by rewrite /E48I => t _; fprops.
move : Exercise4_7d => aux2.
have p10:inc (chrf x) ((substrate E48AJIo) -s1 E48z).
  apply /setC1_P;split; [ue | move=> h; move: p7; rewrite h / E48z; rewrite LfV//; fprops].
have p11:inc (chrf y) ((substrate E48AJIo) -s1 E48z).
  apply /setC1_P;split; [ue | move=> h; move: p9; rewrite h / E48z; rewrite LfV//; fprops].
have chrf1: forall x, inc x (substrate r) ->
  function_prop (chrf x) (substrate E48Js) (substrate E48Io).
  move => z zsr; split; first by apply: char_fun_f.
    by rewrite /chrf /char_fun  q2; aw. 
  by rewrite /chrf /char_fun q6; aw. 
split.
   move: (chrf1 _ xsr)(chrf1 _ ysr) => [q7 q8 q9] [q10 q11 q12].
   move => h; apply /iorder_gle0P=> //; apply /(imo_gleP _ q5); split;fprops. 
   split => //.
   rewrite q2; apply /Exercise4_8qP; try apply: Exercise4_7q => //.
   exact (Exercise4_7k h).
move /iorder_gleP => [pa pb] /(imo_gleP _ q5)  [_ _ [_ _]].  
rewrite q2; move/(Exercise4_8qP (Exercise4_7q xsr) (Exercise4_7q ysr)).
by apply: Exercise4_7m.
Qed.


(** Let [M(x)] be the set of minimal elements that are [>x]. 
If [y] is in [M(x)] then [S(x)] is a strict subset of [S(y)] and there is [z]
such that [z] is in [S(y)] but not in [S(x)]. These elements [z] are 
uncomparable, and the number of such [z] is the cardinal of [M(x)].
*)

Definition all_uncomp_inP K :=
  sub K E48P /\ forall x y, inc x K -> inc y K -> gle r x y -> x = y.

Definition minimal_in_int x a :=
   glt r x a /\  (forall b, glt r x b -> gle r b a -> b = a).

Definition minimals x :=  Zo (substrate r) (minimal_in_int x).


Lemma Exercise4_8t x: inc x (substrate r) ->
  exists K, all_uncomp_inP K /\  K \Eq (minimals x).
Proof.
move=> xsr.
pose f y := choose (fun z => inc z (E47S r y) /\ ~ inc z  (E47S r x)).
move: lr => [or _ ].
have fpr: forall y, inc y (minimals x) ->
  (inc (f y)  (E47S r y) /\ ~ inc (f y) (E47S r x)).
  move=> y ysr; apply choose_pr.
  move: ysr => /Zo_P [ysr [[xle xney] ymin]].
  move: (Exercise4_7k xle) => p1. 
  case: (emptyset_dichot ((E47S r y) -s (E47S r x))) => ne.
    move: (Exercise4_7m ysr xsr (empty_setC ne)) => yx.
    case: xney;  order_tac.
  by move:ne => [z] /setC_P aux; exists z.
 have fpr1: forall y, inc y (minimals x) -> sup r x (f y) = y.
  move=> y ysm; move: (fpr _ ysm) => [p1 p2].
  move: p1 =>/Zo_P  [fsr [firr le1]].
  move: (lattice_sup_pr lr xsr fsr) => [p3 p4 p5].
  have p9: glt r x (sup r x (f y)).
    split => //; dneg xs; apply: Zo_i => //; split => //; ue.
  move: ysm => /Zo_P [p6 [p7 p8]].
  apply: p8 => //; apply: p5 => //; order_tac.
set K:= fun_image (minimals x) f.
have KP: sub K E48P.
  move=> t /funI_P  [z zm ->]; move: (fpr _ zm).
  move => [] /Zo_P [p1 [p2 p3]] p4; apply /setC1_P;split; first by apply: Zo_i.
  dneg fzl; apply /Zo_P;split => //; split => //; rewrite fzl.
  by move: (the_least_pr or  Exercise4_7c) => [_ tle]; apply: tle.
have auK: all_uncomp_inP K.
  split => // u v /funI_P [y ym ->] /funI_P [z zm ->] le1.
  move:(fpr _ ym)(fpr _ zm)=> [] /Zo_P [p1 [p2 p3]] p4 [] /Zo_P [p5 [p6 p7]] p8.
  move: (lattice_sup_pr lr xsr p1) => [_ _ q2].
  move: (lattice_sup_pr lr xsr p5) => [q1 q4 _].
  have: gle r (sup r x (f y)) (sup r x (f z)) by apply: q2 => //; order_tac.
  rewrite (fpr1 _ ym) (fpr1 _ zm) => le2.
  move: ym zm => /Zo_P [r1 [r2 r3]] /Zo_P [r4 [r5 r6]].
  by move: (r6 _ r2 le2) => ->.
exists K;split => //; apply: EqS;exists (Lf f (minimals x) K);saw.
apply: lf_bijective.
    move => t ts; apply /funI_P; ex_tac.
  by move=> u v um vm sf; rewrite  -(fpr1 _ um) -(fpr1 _ vm) sf.
by move=> y /funI_P.
Qed.

(** Converse: if [M] is a set of uncomparable elements of [P], with [k]
elements, there is [x] such that [set_of_minimal x] has at least [k] elements.*)

Lemma Exercise4_7c1:  exists a, greatest r a.
Proof.
move: (finite_set_maximal1 (@sub_refl (substrate r)) nes).
move=> [x xsr xp]; exists x;split => //.
move=> u usr; move: (lattice_sup_pr lr usr xsr); move=> [p1 p2 p3].
move: lr => [or _].
have isr:inc (sup r u x) (substrate r) by order_tac.
by move: (xp _ isr p2) => aux; rewrite - aux in p1.
Qed.

Lemma Exercise4_7i1 x: sub x (substrate r) ->
  has_infimum r x.
Proof.
move: Exercise4_7b => or xr; case: (emptyset_dichot x) => nex.
  move: (the_greatest_pr or  Exercise4_7c1) => tlp.
  rewrite nex; exists (the_greatest r).
  rewrite glb_set0 //.
by apply:  (lattice_finite_inf2 lr  (sub_finite_set xr fs) nex xr). 
Qed.

Lemma Exercise4_8u: infimum r emptyset = the_greatest r.
Proof.
move: Exercise4_7b => or.
move: (the_greatest_pr or  Exercise4_7c1) => tlp.
have ok: (sub emptyset (substrate r)) by fprops.
move:  (infimum_pr1 or (Exercise4_7i1 ok)).
rewrite (glb_set0) // => tlp1.
by apply: (unique_greatest or).
Qed.

Lemma distributive_rec x T:
  inc x (substrate r) -> sub T (substrate r) ->
  sup r x (infimum r T) = infimum r (fun_image T (fun z => sup r z x)).
Proof.
move: Exercise4_7b => or xsr Tsr.
move: (sub_finite_set Tsr fs) => ft; move: T ft Tsr.
apply: finite_set_induction0.
  move=> ok;set im:= fun_image _ _; have ->: im = emptyset.
    by rewrite /im; apply /set0_P => y /funI_P [z /in_set0]. 
  rewrite Exercise4_8u.
  move: (the_greatest_pr or  Exercise4_7c1) => [_ tlp].
  by move: (tlp _ xsr) => aux; apply: (sup_comparable1 or aux).
move=> K a hrec naK sKas.
have Ksr: sub K (substrate r) by apply: (@sub_trans  (K +s1 a)); fprops.
have asr: inc a (substrate r) by apply: sKas; fprops.
move: (Exercise4_7i1 Ksr) => his.
set aux:= fun_image _ _.
set K1 := (fun_image K (fun z : Set => sup r z x)).
have K1sr:sub K1 (substrate r).
  move => t /funI_P [z zK ->]. 
  move: (lattice_sup_pr lr (Ksr _ zK) xsr) => [p1 _ _]; order_tac.
move: (Exercise4_7i1 K1sr) => K1is.
move: (lattice_sup_pr lr asr xsr) => [p1a p2a p3a].
have saxr: inc (sup r a x) (substrate r) by order_tac.
have ->: aux = K1 +s1 (sup r a x).
   set_extens t.
      move /funI_P => [z zt ->]. 
      case /setU1_P: zt => s; apply /setU1_P; [left  |right; ue].
      apply /funI_P; ex_tac.
   case /setU1_P => h; apply /funI_P.
     move /funI_P: h => [z za zb]; exists z;fprops.
   rewrite h; exists a;fprops.
rewrite (infimum_setU1 lr Ksr his asr) (infimum_setU1 lr K1sr K1is saxr).
move: (infimum_pr1 or his) => /(glbP or Ksr) [[p1K p2K] p3K]. 
move: (distributive_lattice_prop2 lr) => [_ p1 _].
by rewrite ((p1 dl3) _ _ _ xsr p1K asr)  (hrec Ksr) -/K1 sup_C.
Qed.


Lemma Exercise4_8v K: all_uncomp_inP K -> exists x,
  inc x (substrate r) /\ 
   (cardinal K) <=c (cardinal (minimals x)).
Proof.
move=> [kp1 kp2].
(** For each [x] in [K], we consider [f(x)] the supremum of the 
complement of [x] in [K]. If [u] is the sup of [K] we have [f(x) < u]. *)
pose c x := K -s1 x.
have Ks: sub K (substrate r). 
  by move => t tk;move: (kp1 _ tk) =>/setC1_P [] /Zo_P [].
have cp: forall x, inc x K -> sub (c x) (substrate r).
  by rewrite /c => x xK t /setC1_P [tK _]; apply: Ks.
pose f x:= supremum r (c x).
set u := supremum r K.
have fpr0: forall x, inc x K -> least_upper_bound r (c x) (f x).
  by move => x xK;move: (supremum_pr1 (proj1 lr) (Exercise4_7i(cp _ xK))). 
have fpr1: forall x, inc x K -> u = sup r (f x) x.
  move => x xK; move: (cp _ xK) => asr.
  move: (supremum_setU1 lr asr (Exercise4_7i asr) (Ks _ xK)).
  by rewrite  {1} /c  (setC1_K xK).
move: lr => [or _].
have fpr2: forall x, inc x K -> glt r (f x) u.
  move => x xK;move: (cp _ xK) => csr; move: (fpr0 _ xK).
  move => /(lubP or csr) [[fs1 _] _]. 
  move: (lattice_sup_pr lr fs1 (Ks _ xK)) => [p1 p2 p3].
  split; first by rewrite (fpr1 _ xK); apply: p1.
  move=> fxu; rewrite -(fpr1 _ xK) -fxu in p2.
  have six: sup_irred r x.
    by  move: (kp1 _ xK) => /setC1_P [] /Zo_P [].
  have Kir: sub K (irreds r) by apply: (@sub_trans E48P) => //; apply: sub_setC.
  have cir: sub (c x)  (irreds r). 
     apply: (@sub_trans  K) => //; apply: sub_setC.
  case: (emptyset_dichot (c x)) => ec; last first.
    move: (Exercise4_8c1 (Ks _ xK) six cir p2 ec).
    by move=> [v ] /setC1_P [vK vx] xv;case: vx; move: (kp2 _ _ xK vK xv).
  move: (fpr0 _ xK); rewrite ec lub_set0 // fxu => lu.
  have Ksx: K = singleton x.
    by apply: set1_pr => //  t tk; ex_middle tx; empty_tac1 t; apply /setC1_P. 
  move: (supremum_singleton or (Ks _ xK)); rewrite -Ksx -/u => ux.
  move: (kp1 _ xK) => /setC1_P [_]; case.
  move: (the_least_pr or Exercise4_7c) => ol.
  by apply: (unique_least or) => //; rewrite - ux.
(**  Assume [x] and [y] distinct in [K]; Then obviously [x <= f(y)] and 
[sup(f(x),f(y))=u]; Thus [f] is injective. *)

have fpr3: forall x y, inc x K -> inc y K -> x <> y ->  gle r x (f y).
  move => x y xK yK xy; move: (cp _ yK) => cK; move: (fpr0 _ yK).
  by move=> /(lubP or cK) [[_ ub] _]; apply: ub; apply /setC1_P.
have fpr4: forall x y, inc x K -> inc y K -> x <> y ->
  sup r (f x) (f y) = u.
  move=> x y xK yK xy. 
  move: (fpr2 _ xK) (fpr2 _ yK) => [p1 _] [p2 _].
  have fxs: inc (f x) (substrate r) by order_tac.
  have fys: inc (f y) (substrate r) by order_tac.
  move: (lattice_sup_pr lr fxs fys) => [p3 p4 p5].
  move: (p5 u p1 p2) => p6.
  have p7: gle r u (sup r (f x) (f y)).
    rewrite (fpr1 _ xK).
    move: (lattice_sup_pr lr fxs  (Ks _ xK)) => [p3a p4a p5a].
    apply: p5a => //; move: (fpr3 _ _ xK yK xy) => aux; order_tac.
  order_tac.
have fpr5: forall x y, inc x K -> inc y K -> f x = f y -> x = y.
   move=> x y xK yK sf; ex_middle xny;  move: (fpr2 _ xK) => [ _ ]; case.
   have fxs:inc (f x) (substrate r) by move: (fpr2 _ xK) => xx; order_tac.
   by move: (fpr4 _ _ xK yK xny); rewrite /sup - sf supremum_singleton.
(** Let [L] be the set of all these [f(x)].
We set [v] the be the infimum of [L], [g(x)] the infimum 
of the complement of [x] in [L]. The same argument as above says [v < g(x)]  *)
set L := fun_image K f.
have lp1: sub L (substrate r).
  move=> t /funI_P [z zK ->]; move: (fpr2 _ zK) => xx; order_tac.
have ->: cardinal K = cardinal L.
  apply /card_eqP.
  exists (Lf f K L); saw ;apply: lf_bijective; aw; trivial.
    move=> t tK; apply /funI_P; ex_tac.
  by move=> y /funI_P.
pose d x := L -s1 x.
have dp: forall x, inc x L -> sub (d x) (substrate r).
  by rewrite /d => x xK t /setC1_P [tK _]; apply: lp1.
pose g x:= infimum r (d x).
set v := infimum r L.
have lp2: forall x, inc x L -> greatest_lower_bound r (d x) (g x).
  by move => x xK;move: (infimum_pr1 or (Exercise4_7i1 (dp _ xK))). 
have lp3: forall x, inc x L -> v = inf r (g x) x.
  move => x xK; move: (dp _ xK) => asr.
  move: (infimum_setU1 lr asr (Exercise4_7i1 asr) (lp1 _ xK)).
  by rewrite  {1} /d  (setC1_K xK).
have lp4: forall x, inc x L -> glt r v (g x).
  move => x xL;move: (dp _ xL) => csr; move: (lp2 _ xL).
  move /(glbP or csr) => [[fs1 _] _]. 
  move: (lattice_inf_pr lr fs1 (lp1 _ xL)) => [p1 p2 p3].
  split; first by rewrite (lp3 _ xL); apply: p1.
  move=> gxv; rewrite -(lp3 _ xL) gxv in p2.
  move: (sup_comparable1 or p2); rewrite sup_C. 
  rewrite (distributive_rec (lp1 _ xL) csr).
  set aux2 := fun_image _ _.
  case: (emptyset_dichot (d x)) => de.
    have -> : aux2 = emptyset.
      by apply /set0_P => y; rewrite /aux2 de => /funI_P [z /in_set0].
    move: (the_greatest_pr or Exercise4_7c1) => ol.
    move: xL => /funI_P [z zK fz] ie.
    move: (fpr2 _ zK) ol;rewrite -Exercise4_8u ie fz; move => lt [_ xv].
    have usr: inc u (substrate r) by order_tac.
    by move: (xv _ usr) => le2; order_tac.
  move: de => [y yd].
  have: inc (sup r y x) aux2 by apply /funI_P;ex_tac.
  move: yd xL => /setC1_P [] /funI_P [z1 z1k eq1] yx /funI_P [z2 z2K eq2].
  have nz12: z1 <> z2 by dneg z12; rewrite eq1 eq2; ue.
  rewrite eq1 eq2 fpr4 // => ua.
  have ->: aux2 = singleton u.
    apply: set1_pr => // t /funI_P [z zd ->].
    move : zd => /setC1_P [] /funI_P [s sk fs3] zx.
    by rewrite fs3 eq2; apply fpr4 => // => h; case: zx; rewrite  fs3 h.
  move: (fpr2 _ z2K) => [lt2 ne2].
  have usr: inc u (substrate r) by order_tac.
  by rewrite -/(inf r u u)  inf_comparable1=> //; [ apply:nesym  | order_tac].
have lp5: forall x y, inc x L -> inc y L -> x <> y ->  gle r (g y) x.
  move => x y xL yL xy; move: (dp _ yL) => cL; move: (lp2 _ yL).
  move=> /(glbP or cL) [[_ ub] _]; apply: ub; apply /setC1_P;split => //.
have lp6: forall x y, inc x L -> inc y L -> x <> y -> inf r (g x) (g y) = v.
  move=> x y xL yL xy. 
  move: (lp4 _ xL) (lp4 _ yL) => [p1 _] [p2 _].
  have fxs: inc (g x) (substrate r) by order_tac.
  have fys: inc (g y) (substrate r) by order_tac.
  move: (lattice_inf_pr lr fxs fys) => [p3 p4 p5].
  move: (p5 v p1 p2) => p6.
  have p7: gle r (inf r (g x) (g y)) v.
    rewrite (lp3 _ xL).
    move: (lattice_inf_pr lr fxs (lp1 _ xL)) => [p3a p4a p5a].
    apply: p5a => //; move: (lp5 _ _ xL yL xy) => aux; order_tac.
  order_tac.
(** Since [v< g(x)] we can choose [h(x)] such that [x< h(x) <= g(x)] and 
[h(x)] minimal in the interval. This is an injective function (since
[inf(h(a),h(b)) <= inf(g(a),g(b)) = v]. *)
pose h x := choose (fun a => gle r a (g x) /\ minimal_in_int v a).
have lp7: forall x, inc x L -> (gle r (h x) (g x) /\ minimal_in_int v (h x)).
  move=> x xL; apply choose_pr.
  set U:= Zo (substrate r) (fun a => glt r v a /\ gle r a (g x)).
  have Usr: sub U (substrate r) by apply: Zo_S.
  have neU: nonempty U. 
    move:(lp4 _ xL) => lt1;exists (g x); apply: Zo_i=> //;try order_tac. 
    split => //; order_tac; order_tac.
  move: (finite_set_minimal1 Usr neU) => [a aU etc]. 
  move: aU => /Zo_P [a1 [a2 a3]].
  exists a; split => //; split => // b bv ba. 
  apply: etc => //; apply: Zo_i => //; try split => //; order_tac. 
set M := fun_image L h.
have Mm: sub M (minimals v).
  move=> t /funI_P [z zL ->]; move: (lp7 _ zL) => [p1 p2]. 
  apply: Zo_i => //; order_tac.
have ->: cardinal L = cardinal M.
  apply /card_eqP; exists (Lf h L M); saw; apply: lf_bijective.
      move=> t tL; apply /funI_P; ex_tac.
    move => a b aL bL sh.
    move: (lp7 _ aL) (lp7 _ bL) => [p1 [p2 p3]] [p4 [p5 p6]].
    ex_middle nab;rewrite - sh in p4.
    have gasr: inc (g a) (substrate r) by order_tac.
    have gbsr: inc (g b) (substrate r) by order_tac.
    move: (lattice_inf_pr lr gasr gbsr)=> [g1 g2 g3].
    move: (g3 _  p1 p4); rewrite (lp6 _ _ aL bL nab) => g4;order_tac.
  by move=> y /funI_P.
(** Obvioulsy [v] is a solution *)
exists v;split => //; last by apply: sub_smaller.
by move: (infimum_pr1 or (Exercise4_7i1 lp1)) => /(glbP or lp1) [[ok _] _].
Qed.

End Irred_lattice.

(** ---- Exercise 4.9 Let [E] be a distributive lattice, [A] a sublattice
(invariant by sup and inf). Then [A] is isomorphic to a sublattice
of a product of [n] totally ordered sets iff the maximal cardinal of a free
subset containing only ireeducible elements is [n].

We first characterise the sup and inf in a product. We show that the product
of dlattices is a dlattice, that the product of totally ordered sets is
a dlattice. *)

Lemma setX_lattice_sup g (r :=  order_product g) x y 
   (z := sup r x y) (t := inf r x y):
  order_fam g -> (allf g lattice) ->
  inc x (substrate r) -> inc y (substrate r) ->
  [/\ inc z (substrate r),
    inc t (substrate r),
    (forall i, inc i (domain g) -> Vg z i = sup (Vg g i)(Vg x i) (Vg y i)) &
    (forall i, inc i (domain g) -> Vg t i = inf (Vg g i)(Vg x i) (Vg y i))].
Proof.
move => ofg alg xsr ysr.
move: (setX_lattice ofg alg) => []; rewrite -/r => or hr.
move: (hr _ _ xsr ysr); set xy:= doubleton x y; move => [hs hi].
have zsr: inc z (substrate r).
  by move: (sup_pr or xsr ysr hs) => [pa _ _]; rewrite /z; order_tac.
have tsr: inc t (substrate r).
  by move: (inf_pr or xsr ysr hi) => [pa _ _]; rewrite /t; order_tac.
move: (xsr) (ysr); rewrite {1 2} (proj2(order_product_osr ofg)) => xsr1 ysr1.
have sd: sub xy (prod_of_substrates g) by move=> u; case /set2_P => ->. 
move: (sup_in_product ofg sd) => [pa pb].
move: hs;rewrite -pa; move => hs; move: (pb hs) => hz.
move: (inf_in_product ofg sd) => [pc pd].
move: hi;rewrite -pc; move => hi; move: (pd hi) => ht.
clear pa pb pc pd hs hi.
have fgf: fgraph (fam_of_substrates g) by rewrite /fam_of_substrates; fprops.
have aidf: forall i, inc i (domain g) -> 
   [/\ inc i (domain (fam_of_substrates g)),
     function (pr_i (fam_of_substrates g) i),
    sub xy (source (pr_i (fam_of_substrates g) i)) &
    Vfs (pr_i(fam_of_substrates g) i) xy = doubleton (Vg x i) (Vg y i)].
   move => i idg.
    have id:  inc i (domain (fam_of_substrates g)).
         by rewrite /fam_of_substrates; aw.
    have fp: function (pr_i (fam_of_substrates g) i) by fprops.
    have sxy: sub xy (source (pr_i (fam_of_substrates g) i)).
      by rewrite /pr_i; aw.
   split => //; set_extens u.
     move => /(Vf_image_P fp sxy) [w wxy ->]. 
     move: (sxy _ wxy); rewrite {1} /pr_i lf_source => ws.
     rewrite pri_V //; move: wxy;case /set2_P => ->; fprops.
  have ixxy: inc x xy by rewrite /xy; fprops.
  have iyxyy: inc y xy by rewrite /xy; fprops.
  by case /set2_P=> ->; apply /(Vf_image_P fp sxy);
     [exists x | exists y] => //;rewrite pri_V. 
split => //.
  move => i idg; move: (f_equal (Vg^~ i) hz); rewrite !LgV//; move => ->.
  by move: (aidf _ idg) => [qa qb qc ->].
move => i idg; move: (f_equal (Vg^~i) ht); rewrite !LgV//; move => ->.
by move: (aidf _ idg) => [qa qb qc ->].
Qed.

Lemma setX_dlattice g:
  order_fam g -> (allf g lattice) ->
   (allf  g  distributive_lattice1) ->
  distributive_lattice1 (order_product g).
Proof.
move => pa pb pc; move:  (setX_lattice pa pb) => lp.
move => x y z; set r := (order_product g) => xsr ysr zsr.
move: (setX_lattice_sup pa pb ysr zsr); rewrite -/r.
set yz := inf r y z; move=> [ _ yzsr _ yzv].
move: (setX_lattice_sup pa pb xsr ysr); rewrite -/r.
set xy := sup r x y; move=> [ xysr _ xyv _ ].
move: (setX_lattice_sup pa pb xsr zsr); rewrite -/r.
set xz := sup r x z; move=> [ xzsr _ xzv _ ].
move: (setX_lattice_sup pa pb xsr yzsr); rewrite -/r.
set xyz := sup r x yz; move=> [ xyzsr _ xyzv _ ].
move: (setX_lattice_sup pa pb xysr xzsr); rewrite -/r.
set xyxz := inf r xy xz; move=> [ _ xyxzsr _ xyxzv].
have aux: forall t, inc t (substrate r) -> [/\ fgraph t, domain t = domain g &
   forall i, inc i (domain g) -> inc (Vg t i) (substrate (Vg g i))].
  move => t ; rewrite /r (proj2(order_product_osr pa)) /prod_of_substrates.
  have pd: fgraph (fam_of_substrates g) by rewrite /fam_of_substrates; fprops.
  move/setXb_P; aw; move => [fgt dt hh]; split => //.
  move => i idt; move: (hh _ idt); rewrite LgV//; ue.
move: (aux _ xyzsr) (aux _ xyxzsr) => [g1 d1 v1] [g2 d2 v2].
apply: fgraph_exten => // ; [ ue | rewrite d1 => i idg].
move:  (aux _ xsr) (aux _ ysr) (aux _ zsr). 
move => [_ _ xsi][_ _ ysi][_ _ zsi].
move: (xsi _ idg)(ysi _ idg)(zsi _ idg) => xsa ysa zsa.
rewrite (xyxzv  _ idg) (xyzv _ idg) (yzv _ idg)  (xyv _ idg) (xzv _ idg).
rewrite (pc _ idg) //.
Qed.

Lemma setX_torder_dlattice g:
  order_fam g -> (allf g total_order) ->
  (lattice (order_product g) /\  distributive_lattice1 (order_product g)).
Proof.
move => ofg alg.
have aux: forall i, inc i (domain g) -> lattice (Vg g i).
  move => i idg; move: (alg _ idg); apply: total_order_lattice.  
split; first by apply: setX_lattice => //.
apply: setX_dlattice => //.
move => i idg; move: (alg _ idg); apply: total_order_dlattice.  
Qed.

Lemma setX_lattice_finite_sup 
   g (r :=  order_product g) E (z := supremum r E):
  order_fam g -> (forall i, inc i (domain g) -> lattice (Vg g i)) ->
  finite_set E -> sub E (substrate r) -> nonempty E ->
  (inc z (substrate r) /\
    forall i, inc i (domain g) -> Vg z i = supremum (Vg g i)(fun_image E (Vg^~i))).
Proof.
move => ofg alg fsE sEs neE.
move: (setX_lattice ofg alg) => lp.
move: (lattice_finite_sup2 lp fsE neE sEs) => hs.
move: (supremum_pr (proj1 lp) sEs hs) => []; rewrite -/r -/z => pa pb.
move: pa => [pa1 pa2]; split; first by exact.
move => i idg.
have pc: sub E (productb (fam_of_substrates g)).
  by move: sEs; rewrite (proj2 (order_product_osr _)) /prod_of_substrates.
move: (sup_in_product ofg pc) => [ha hb].
move: hs; rewrite - ha => hc; rewrite /z /r (hb hc); aw; rewrite LgV//. 
have fgf: fgraph (fam_of_substrates g) by rewrite /fam_of_substrates; fprops.
have idf: inc i (domain (fam_of_substrates g)) by rewrite /fam_of_substrates;aw.
have fp: function (pr_i (fam_of_substrates g) i) by fprops.
have sE: sub E (source (pr_i (fam_of_substrates g) i)) by rewrite /pr_i; aw.
congr (supremum (Vg g i) _); set_extens t.
  move => /(Vf_image_P fp sE)  [y ye ->]; apply /funI_P;ex_tac.
  by rewrite pri_V //;  apply:pc.
move /funI_P =>  [y ye ->]; apply  /(Vf_image_P fp sE).
ex_tac;by rewrite pri_V //;  apply:pc.
Qed.


(** We say that [A] is a sublattice if the sup and and of two 
elements of [A] is in [A]. If [E] is a lattice, then [A] is a lattice,
sup and inf coincide *)

Definition sublattice r A :=
   forall x y, inc x A -> inc y A -> (inc (sup r x y) A /\ inc (inf r x y) A).


Lemma sublattice_pr r A (rA:= induced_order r A):
  lattice r -> sublattice r A -> sub A (substrate r)->
  [/\ lattice rA, substrate rA = A,
   (forall a b, inc a A -> inc b A -> sup r a b = sup rA a b) &
   (forall a b, inc a A -> inc b A -> inf r a b = inf rA a b) ].
Proof.
move => lr sla sa.
move: (lr) => [or lr1].
move: (iorder_osr or sa) => [orA srA].
have auxP: forall a b, inc a A -> inc b A -> (gle rA a b <-> gle r a b). 
   move => a b aA bA; exact :(iorder_gle0P _ aA  bA).
have pa: forall a b, inc a A -> inc b A ->
  (least_upper_bound rA (doubleton a b) (sup r a b) /\
   greatest_lower_bound rA (doubleton a b) (inf r a b)).
  move => a b aA bA.
  have da: sub (doubleton a b) (substrate rA).
    by move => t /set2_P [] ->; rewrite srA.
  move: (lr1 _ _ (sa _ aA) (sa _ bA)) => [ta tb].
  move: (sup_pr or (sa _ aA) (sa _ bA) ta) => [s1 s2 s3].
  move: (inf_pr or (sa _ aA) (sa _ bA) tb) => [s4 s5 s6].
  move: (sla _ _ aA bA)=> [s7 s8]; split.
    apply /(lubP orA da); rewrite /upper_bound  srA;split => //.
      by split => //;move => y /set2_P [] ->; apply /auxP.
    move => z [zA sz]; apply /auxP => //; apply: s3;
       apply /auxP=> //; apply: sz; fprops.
  apply /(glbP orA da); rewrite /lower_bound  srA;split => //.
      by split => //;move => y /set2_P [] ->; apply /auxP.
  move => z [zA sz]; apply /auxP=> //; apply: s6;
  apply /auxP => //; apply: sz; fprops.
split => //.
+ split; first by exact.
  rewrite srA; move => x y xA yA; move: (pa _ _ xA yA)=> [qa qb].
  split; [ by exists (sup r x y) | by exists (inf r x y)].
+ move => x y xA yA; move: (pa _ _ xA yA)=> [qa qb].
  exact (supremum_pr2 orA qa).
+ move => x y xA yA; move: (pa _ _ xA yA)=> [qa qb].
  exact (infimum_pr2 orA qb).
Qed.

Lemma sublattice_dr r A :
  lattice r -> sublattice r A -> sub A (substrate r)->
  distributive_lattice1 r ->
  distributive_lattice3 (induced_order r A).
Proof.
move=> lr slr sard dl1.
move: (sublattice_pr lr slr sard) => [lA srA sA iA].
have pa: distributive_lattice1 (induced_order r A).
  move => x y z; rewrite srA => xA yA zA.
  rewrite - (sA _ _ xA zA) - (sA _ _ xA yA) - (iA _ _ yA zA).
  move:(proj1 (slr _ _ xA yA)) (proj1 (slr _ _ xA zA)) => xyA xzA.
  rewrite - (iA _ _ (proj1 (slr _ _ xA yA)) (proj1 (slr _ _ xA zA))).
  rewrite - (sA _ _ xA (proj2 (slr _ _ yA zA))).
  exact (dl1 _ _ _ (sard _ xA)(sard _ yA)(sard _ zA)).
exact (proj1 (distributive_lattice_prop1 lA) pa).
Qed.

Lemma Exercise4_9a g n A  (r := order_product g):
   order_fam g -> (allf g total_order) ->
   natp n -> cardinal (domain g) = n -> n <> \0c ->
   sub A (substrate r) -> sublattice r A ->
   forall B, free_subset r B ->
      (forall x, inc x B -> sup_irred (induced_order r A) x) ->
      sub B A -> cardinal B <=c n.
Proof.
move => ofg alg nN cdg nz asr slA B frB aiB sbA.
have cn: cardinalp n by fprops.
have snb: natp (csucc n) by fprops.
move: (setX_torder_dlattice ofg alg) => [lg dlg].
(** proof by contradiction. if false, there is a set [C] with [n+1] elements
and we forget about [B] *)
case: (cleT_el (CS_cardinal B) cn) => // lncB.
have [C CB cs]: exists2 C, sub C B & cardinal C = csucc n.
  have pa: cardinal(csucc n) <=c cardinal B.
    rewrite (card_nat snb).
    case: (finite_or_infinite (CS_cardinal B)).
      by move /NatP => fb; apply/cleSltP.
    by move => ib; apply: cle_fin_inf => //; apply /NatP.
  move: (cardinal_le_aux1 pa) => /(eq_subset_cardP (csucc n)). 
  move/set_leP => [C CB eq]; exists C => //. 
  by symmetry;rewrite - (card_nat snb); apply /card_eqP.
have scA: sub C A by apply: sub_trans CB sbA.
have aiC : forall x, inc x C -> sup_irred (induced_order r A) x.
  by move => x xc; exact (aiB _ (CB _ xc)).
have frC: free_subset r C.
  by move => x y xc yc xy; move: (CB _ xc) (CB _ yc) => xb yb; apply:frB.
apply: False_ind.
clear frB aiB sbA lncB CB B.
(** To each index, we associate [x] in [C] such that [x(i)] is maximal *)
pose mip i x := inc x C /\
    forall y, inc y C -> gle (Vg g i) (Vg y i) (Vg x i).
have fsC: finite_set C by hnf; rewrite cs; apply /NatP.
have pa: forall i, inc i (domain g) -> exists x, mip i x.
  move => i idg.
  set E := fun_image C (Vg^~i).
  move: (alg _ idg) => toi.
  have fse: finite_set E by apply: finite_fun_image.
  have ser: sub E (substrate (Vg g i)).
     move => t /funI_P [z zC ->].
     move: (asr _ (scA _ zC)); rewrite /r (proj2(order_product_osr ofg)).
     move/prod_of_substratesP => [fgz dz h].
     apply: h => //;ue.
  have [c cC]: nonempty C.
    case: (emptyset_dichot C) => // ec.
    by move: cs; rewrite ec  cardinal_set0 => nez; case: (@succ_nz n).
  have ne: nonempty E by exists (Vg c i); apply /funI_P; ex_tac.
  move: (finite_subset_torder_greatest toi fse ne ser) => [x []].
  move: toi => [oi oit].
  rewrite (iorder_sr oi ser) => xe xge.
  move: xe => /funI_P [z zC zv]; exists z; split => //.
  rewrite - zv; move => y yC.
  have ye: inc (Vg y i) E by  apply /funI_P;ex_tac.
  exact (iorder_gle1 (xge _ ye)).
pose mx i := choose (fun x => mip i x).
have mxp: forall i, inc i (domain g)-> mip i (mx i).
  move => i idg; rewrite /mx; apply: (choose_pr (pa _ idg)).
have pb: forall i, inc i (domain g) -> inc (mx i) C.
  move => t ta;  exact: (proj1 (mxp _ ta)).
(** Since [C] is big, one element is not of the form [mx i], say it is [x].
  let [xb] be the sup of the complement of [x] in [C]. Then [x <= xb]
 *)
have [x xC xne]: exists2 x, inc x C & forall i, inc i (domain g) -> mx i <> x.
  set f := Lf mx (domain g) C.
  have ff: function f by apply: lf_function.
  move: (Imf_Starget ff); rewrite {2}/f; aw => s1.
  case: (equal_or_not (Imf f) C) => h.
    move: (image_smaller ff); rewrite {2}/f; aw; rewrite cdg.
    by rewrite h cs => /(cltNge (cltS nN)).
  move: (setC_ne (conj s1 h)) => [x] /setC_P [xc xp].
  exists x=> // i idg mi; case: xp; apply /(Imf_P ff).
  by rewrite /f;aw; ex_tac; rewrite LfV//.
set xbs:= C -s1 x.
have sxbsC: sub xbs C by move => t /setC1_P [].
have fsx: finite_set xbs by apply: (sub_finite_set sxbsC fsC).
have nex: nonempty xbs.
  case: (emptyset_dichot xbs) => // xe.
  move: cs.
  have ->: C = singleton x.
    by apply: set1_pr => // t tC; ex_middle tnx; empty_tac1 t; apply /setC1_P. 
  rewrite cardinal_set1 - succ_zero => bad; case: nz.
  by rewrite (csucc_inj CS0 (CS_nat nN) bad).
have allc:(forall i, inc i (domain g) -> lattice (Vg g i)).
   move => i idg; move: (alg _ idg); apply: total_order_lattice.  
move:  (sub_trans sxbsC (sub_trans scA asr)) => scbssr.
move: (setX_lattice_finite_sup ofg allc fsx scbssr nex).
set xb:= (supremum r xbs); rewrite -/r; move => [xbsr xbgr].
have sr: (prod_of_substrates g) = substrate r 
   by rewrite (proj2 (order_product_osr _)).
have xxb: gle r x xb.
  apply /(order_product_gleP); rewrite sr;split => //.
    by apply: asr; apply: scA.
  move => i idg; rewrite (xbgr _ idg).
  move: (mxp _ idg) => [sa sb].
  move: (alg _ idg) => [ori tori].
  suff: least_upper_bound (Vg g i) (fun_image xbs (Vg^~ i)) (Vg (mx i) i).
    by move => h; rewrite - (supremum_pr2 ori h); apply: sb.
  have sc: sub (fun_image xbs (Vg^~ i)) (substrate (Vg g i)).
     move => t /funI_P [z zbs ->].
     move: (scbssr _ zbs); rewrite - sr; move /(prod_of_substratesP). 
     by move => [_ _]; apply.
  have sd: inc  (Vg (mx i) i) (fun_image xbs (Vg ^~i)).
    by apply/funI_P; exists (mx i)=> //; apply /setC1_P;split => //; apply: xne.
  apply /(lubP ori sc); split.
    split; first by apply: sc.
    by move => y /funI_P[z zbs ->]; apply: sb; apply sxbsC.
  by move => z [z1]; apply.
(** Let's rewrite that [x] is irreducible in [A]. We have: if [x<= sup(a,c)]
with [a] in [A] and [c] in [C] then [x  <= a]*)
have exfr: forall a, inc a xbs -> not (ocomparable r x a).
  move => a /setC1_P [aC ax]; case => lxa.
    by move: (frC _ _ xC aC lxa) => naw; case: ax.
    by move: (frC _ _ aC xC lxa). 
move: (sublattice_pr lg slA asr) => [lrA sra supa infa].
move: (sublattice_dr lg slA asr dlg) => dlA.
have hx: forall a b, inc a A -> inc b A ->
   gle r x (sup r a b) -> gle r x a \/ gle r x b.
   move => a b aA bA.
   have auxP: forall a b, inc a A -> inc b A ->
       (gle (induced_order r A) a b <-> gle r a b). 
       by move => s t sA tA; apply: iorder_gle0P.
   move: (Exercise4_8a lrA dlA (aiC _ xC)); rewrite -/r sra => h.
   move: (scA _ xC) => xA.
   move: (proj1 (slA _ _ aA bA)) => sA.
   move /(auxP _ _ xA sA).
   move : (h _ _ aA bA); rewrite - (supa _ _ aA bA) => ra rb.
   by move: (ra rb); case; [left | right ]; apply /auxP. 
have hx1:  forall a b, inc a A -> inc b xbs  ->
   gle r x (sup r a b) -> gle r x a.
  move => a b aA bb sab.
  move: (exfr _ bb) => nc.
  move: bb => /setC1_P [bC _].
  by case: (hx _ _ aA (scA _ bC) sab) => // lxb; case: nc; left.
(** let's write [C] as the set of all [f(i)], and consider 
[s(i+1)= sup (s(i),f(i))], and [s(1) = f(0)] *)
have [f [bf sf tf]]: 
   exists f, bijection_prop f (Nint n) xbs.
  suff: Nint n \Eq xbs => //.
   apply /card_eqP; rewrite (card_Nint nN).
   apply: (csucc_inj  (CS_nat nN) (CS_cardinal _)).
  by rewrite  - (csucc_pr2 xC) cs.
have ff: function f by fct_tac.
pose Ei i := Vfs f (Nint i).
have Eiz: Ei \0c = emptyset.
  have aux: (sub emptyset (source f))by fprops.
  rewrite /Ei Nint_co00. 
  by apply /set0_P =>t /(Vf_image_P ff aux) [s] /in_set0.
have Eis: forall i, inc i Nat -> i <c n -> 
     Ei (csucc i) = (Ei i) +s1 (Vf f i).
  move => i iN sin; rewrite /Ei.
  move: (NS_succ iN) => siN.
  move: (Nint_M iN) => sc.
  have sa: sub (Nint (csucc i)) (source f).
    rewrite sf; apply: Nint_M1 => //.
    by apply /cleSltP.
  have sb: sub (Nint i) (source f) by  exact (sub_trans sc sa).
  set_extens t.
    move /(Vf_image_P ff sa) => [u us ->]; case: (equal_or_not u i) => ui;
    apply /setU1_P; [right; ue | left; apply /(Vf_image_P ff sb) ].
    by exists u => //;move: us => /(NintsP iN) => h; apply/(NintP iN).
  case /setU1_P=> h; apply /(Vf_image_P ff sa).
      move /(Vf_image_P ff sb):h => [z z1 z2]; by exists z=> //; apply: sc.
      by rewrite h; exists i => //;apply: Nint_si.
have zl: \0c <c n by  move: nz => / (strict_pos_P1 nN).
have Eio: Ei \1c = singleton (Vf f \0c).
   rewrite - succ_zero.
   rewrite (Eis _ NS0 zl) Eiz; apply: set1_pr => //; fprops.
   by move => z;case /setU1_P => // /in_set0.
pose sei i := supremum r (Ei i).
have sen: sei n = xb.
  rewrite /sei /Ei - sf -/(Imf _). 
  by rewrite  (surjective_pr0 (proj2 bf)) tf.
have tb: forall i, inc i Nat -> i <c n -> inc (Vf f i) xbs.
  by move => i iN ltin; Wtac; rewrite sf; apply /NintP.
have ns0 := NS0.
have seo: sei \1c = Vf f \0c.
  rewrite /sei Eio (supremum_singleton (proj1 lg)) //.
  apply: scbssr; apply: tb; fprops.
have sel: forall i, natp i -> i <=c n -> i <> \0c ->
    (sub (Ei i) xbs /\ least_upper_bound r (Ei i) (sei i)).
  move => i iN lein inz.
  have sa:sub (Nint i) (source f).
     rewrite sf; apply: Nint_M1 => //. 
  have nei: nonempty (Ei i).
     exists (Vf f \0c); apply /(Vf_image_P ff sa).
      exists \0c => //; apply /NintP => //.
     by apply/ strict_pos_P1.
  have seix: sub (Ei i) xbs by rewrite -tf; apply: (fun_image_Starget1 ff).
  split; first by exact.
  move: (sub_finite_set seix fsx) => fe.
  apply: (supremum_pr1 (proj1 lg)).
  exact(finite_subset_lattice_sup lg fe nei (sub_trans seix scbssr)).
have ses:  forall i, inc i Nat -> i <c n -> i <> \0c ->
     sei (csucc i) = sup r (sei i) (Vf f i).
  move => i iN ltin inz; move: (Eis _ iN ltin) => h.
  move: (sel _ iN (proj1 ltin) inz) => [sa sb].
  have se: has_supremum r (Ei i) by exists (sei i).
  move: (sub_trans sa scbssr) => sc.
  have sd: inc (Vf f i) (substrate r)  by apply: scbssr; apply: tb.
  by move: (supremum_setU1 lg sc se sd); rewrite -h. 
(** Each [s(i)] is in [A]. Thus [x <= s(i+1)] implies [x <= s(i)] 
   By induction [x <= s(1)] absurd *)
suff: gle r x (sei \1c) by rewrite seo=> h;case:(exfr _  (tb _ NS0 zl)); left.
rewrite - sen in xxb;move/cge1P: (zl); move: {-1} \1c (cleR CS1). 
apply: (Nat_induction4 NS1 nN xxb) => i /cge1P  [_ /nesym] inz ltin.
have iN:= (NS_lt_nat ltin nN). 
rewrite (ses _ iN ltin inz); apply: hx1 (tb _ iN ltin).
move: i {ltin } iN (proj1 ltin) inz.
apply: Nat_induction; first by  move => _ [].
move => t tN hrec stn _.
have tn: t <c n  by apply /cleSltP.
have ftA: inc (Vf f t) A by apply/scA /sxbsC /(tb _ tN).
case: (equal_or_not t \0c) => tnz.
    by rewrite tnz succ_zero seo - tnz. 
rewrite (ses _ tN tn tnz);apply (slA _ _ (hrec (proj1 tn)  tnz) ftA).
Qed.

(** Converse. Assume that the maximal number of free subsets
of [P] in [n] in a finite distributive lattice. Then the set [F]
is isomorphic to a sublattice of [n] totally ordered sets. *)

Lemma fun_image_exten x f g:
   (forall t, inc t x -> f t = g t) -> fun_image x f = fun_image x g. 
Proof.
by move => h; set_extens t; move => /funI_P [z zx ->];
  apply /funI_P; ex_tac; rewrite h.
Qed.


Lemma Exercise4_9b r (P := E48P r) n:
  lattice r -> distributive_lattice1 r -> finite_set (substrate r) ->
  nonempty (substrate r) ->
  natp n -> order_width (induced_order r P) n ->
  exists g A f, 
    let r' := (order_product g) in 
    [/\ order_fam g, (allf g total_order), cardinal (domain g) = n,
    sub A (substrate r') & sublattice r' A /\
    order_isomorphism f r (induced_order r' A)].
Proof.
move => lr dlr fsr nesr nN eh.
move: (proj1 lr) => or.
have s1: sub P (substrate r).
  by rewrite /P/E48P => t /setC1_P [] /Zo_P [ok _] _.
move: (iorder_osr or s1) => [orp sr].
(** We first partition [P] into [n] sets. *)
move: (Exercise4_5d orp nN eh) => [X1].
rewrite (iorder_sr or s1); move=> [pX1 cX1 aX1].
have aX2: forall x, inc x X1 -> total_order (induced_order r x).
   move => x x1; move: (aX1 _ x1) => /total_subordersP []; rewrite iorder_sr//  => xssxP.
   by rewrite iorder_trans.
move: (the_least_pr (proj1 lr) (Exercise4_7c lr fsr nesr)).
set zr := (the_least r); move=> [zrr zrl].
(** We exclude the case [n=0], because [P] is empty and [F] is a singleton *)
case: (equal_or_not n \0c) => nnz.
  move: (proj1(proj1 pX1)).
  rewrite nnz in cX1; rewrite (card_nonempty cX1) setU_0 => pe.
  have sis: irreds r = singleton zr.
    rewrite (Exercise4_7f lr fsr nesr); rewrite -/P -pe -/zr.
    by apply: set1_pr => //; fprops; move => z;case /setU1_P => // /in_set0.
  have srs: substrate r = singleton zr.
     apply: set1_pr => // x xr.
     have pa: (E47S r x) = singleton zr.
       apply: set1_pr; first by apply Exercise4_7g.
       move => z /Zo_P [sa [sb _]].
       have : inc z (irreds r) by apply: Zo_i.
       by rewrite sis => /set1_P.
     move: (Exercise4_7l lr fsr nesr xr); rewrite pa.
     by rewrite (supremum_singleton or zrr).
  set g:= Lg emptyset id.
  have c1: order_fam g by  rewrite /g; hnf; aw => x; case; case.
  have c2: (allf g total_order) by rewrite /g; hnf; aw => x /in_set0.
  have c3: cardinal (domain g) = n. 
     by rewrite /g nnz; aw; rewrite cardinal_set0.
  set r' := (order_product g).
  have srr: substrate r' = singleton emptyset. 
    rewrite /r' (proj2 (order_product_osr _)) //.
    rewrite /prod_of_substrates /fam_of_substrates /g; aw.
    by apply: setXb_0'.
  have or': order r' by apply: (proj1 (order_product_osr _)).
  have sr1: singletonp (substrate r) by exists zr.
  have sr2: singletonp (substrate r') by exists emptyset.
  move: (set1_order_is2 or or' sr1 sr2) => [f isf].
  set A := substrate r'.
  have c4: sub A (substrate r')  by fprops.
  exists g, A, f;split => //; split.
    have esr: inc emptyset (substrate r') by  rewrite srr; fprops.
    have aux: gle r' emptyset emptyset by order_tac.
    move => x y; rewrite /A srr => /set1_P -> /set1_P ->.
    rewrite (sup_comparable1 or' aux) (inf_comparable1 or' aux); split;fprops.
  by rewrite iorder_substrate.
(**  To each element of the partition we add [e], the least element of [F]. 
This gives a family of totally ordered sets [Xi] *)
pose Xf i := i +s1 zr.
have sXr: forall x, inc x X1 -> sub (Xf x) (substrate r).
   move => x x1 t;case /setU1_P => xe; last by ue.
   apply: s1; move: pX1 => [[<- pb] pc]; union_tac.
set g:= Lg X1 (fun z => (induced_order r (Xf z))).
have c2:  (allf g total_order).
  rewrite /g; hnf; aw; move => s xs;rewrite LgV//.
  move: (sXr _ xs) => sr'; move: (iorder_osr or sr') => [pa pb].
  split => //; rewrite pb.
  move: (aX2 _ xs) => to1  x y xa ya.
  suff: gle r x y \/ gle r y x by case => le1;[left | right];apply /iorder_gleP.
  have sa: sub s (substrate r).
     apply: sub_trans sr'; move => t; rewrite /Xf; fprops.
  move: xa ; case /setU1_P. 
    move: ya; case /setU1_P.
        move: (proj2 to1); rewrite iorder_sr // => h.
        move => iys ixs; move: (h _ _ ixs iys). 
        case => h1; [left | right]; apply: (iorder_gle1 h1).
     by move => -> ixs; right; apply: zrl; apply: sa.
  by move => ->;  left; apply: zrl; apply: sr'.
have c1: order_fam g  by  hnf;move => x xd; exact (proj1 (c2 _ xd)).
(** Let [gi(x)] be the elements [y] of [Xi] such that [y <= x], and [fi(x)]
    the greatest of these elements. The product of the [fi] will be the iso *)
pose Fo i x := Zo (Xf i) (fun z => gle r z x).
have Fozr:  forall i x, inc x (substrate r) -> inc zr (Fo i x).
   move => i x xsr; apply: Zo_i; [ by rewrite /Xf; fprops | by apply: zrl].
have Fon: forall i x, inc x (substrate r) -> nonempty (Fo i x).
   move => i x xsr; exists zr; apply: (Fozr _ _ xsr).
have Fos: forall i x, inc i X1 -> sub (Fo i x) (substrate (Vg g i)).
 move => i x iX; rewrite /g LgV//; rewrite iorder_sr; fprops; apply: Zo_S.
have Fof: forall i x, inc i X1 -> finite_set (Fo i x).
  move => i x iX;apply: sub_finite_set fsr; apply: sub_trans (sXr _ iX).
  apply: Zo_S.
have For: forall i x, inc i X1 -> sub (Fo i x) (substrate r).
   move => i x iX.
   have sa: sub (Fo i x) (Xf i) by apply: Zo_S.
   apply: (sub_trans sa (sXr _ iX)).
pose fo i x := the_greatest (induced_order r (Fo i x)).
have fop: forall i x, inc i X1 -> inc x (substrate r) ->
   greatest (induced_order r (Fo i x)) (fo i x).
   move => i x iX xsr. 
   have idg: inc i (domain g)  by rewrite /g; aw.
   move: (For _ x iX) => sf.
   move:(c2 _ idg) => tor.
   have sa: sub (Fo i x) (Xf i) by apply: Zo_S.
   have so: (induced_order (Vg g i) (Fo i x)) =  (induced_order r (Fo i x)).
     by rewrite /g LgV//; rewrite iorder_trans.
   have ori: order (induced_order (Vg g i) (Fo i x)).
     by rewrite so;apply: (proj1 (iorder_osr or _)).
   move:(the_greatest_pr (ori) (finite_subset_torder_greatest 
           tor (Fof _ _ iX) (Fon _ _ xsr) (Fos _ _ iX))).
   by rewrite so.
pose fp x := Lg X1 (fun i => fo i x).
set r' := order_product g.
move: (order_product_osr c1) => [ppa ppb].
have ta: forall x, inc x (substrate r) ->  inc (fp x) (substrate r').
   rewrite  ppb /prod_of_substrates /fp/g/fam_of_substrates. 
   move => x xsr; apply/setXf_P;aw;split;fprops.
   move => i iX1; rewrite !LgV//.
   move: (fop _ _ iX1 xsr) => [h _]; move: h.
   move: (sXr _ iX1) => s2.
   have s3: sub (Fo i x) (Xf i) by apply: Zo_S.
   rewrite (iorder_sr or  (sub_trans s3 s2)) (iorder_sr or s2); apply: s3.
set A:= fun_image (substrate r) fp.
have c4: sub A (substrate r'). 
  by rewrite /A; move => t /funI_P [z zsr ->]; apply: ta.
(** We note that [S(x)] is the union of the [gi(x)]. By associativity
 of the sup, and since [x = sup S(x)], we get [x = sup (fi x)].
  We deduce that [f] is an order isomorphism *)
case: (emptyset_dichot X1) => X1ne.
   by case: nnz;rewrite - cX1 X1ne cardinal_set0.
move: (X1ne) => [repX repXX].
have sxp: forall x, inc x (substrate r) ->  
    E47S r x = unionb (Lg X1 (fun i => Fo i x)).
   move: pX1 => [[pa pc] pb].
   move => x xsr; set_extens t. 
     move /Zo_P => [tsr [si le1]]; apply /setUb_P; aw.
     case: (equal_or_not t zr).
       by move => ->; exists repX => //; rewrite LgV//; apply: Fozr.
     move => ntz.
     have : inc t P by  apply: Zo_i; [ apply: Zo_i | move /set1_P].
     rewrite -pa => /setU_P [y ty yx];ex_tac; rewrite LgV//; apply: Zo_i => //.
     rewrite /Xf; fprops.
  move => /setUb_P [y ]; rewrite Lgd=> y1; rewrite LgV//; move=>/Zo_P. 
  rewrite /Xf; aw; move => [sa sb]; case/ setU1_P: sa => ty; apply /Zo_P.
    have: inc t P by rewrite  -pa; union_tac.
    by move => /Zo_P [] /Zo_P [ra rb] _.
  move: (Exercise4_7d lr fsr nesr) => /Zo_P. 
  by  rewrite  -/zr; move => [sc sd]; split => //; ue.
have sxp1: forall x, inc x (substrate r) -> 
     x = supremum r (fun_image X1 (fun l  => supremum r (Fo l x))).
  move => x xsr; move: (sxp _ xsr) => aux.
  set X :=  (Lg X1 (Fo^~ x)).
  move: (f_equal (supremum r) aux). 
  rewrite (Exercise4_7l lr fsr nesr xsr).
  have suXdr: sub (unionb X) (substrate r).
    move =>z /setUb_P; rewrite /X; aw;move => [y yx1]; rewrite LgV// => /Zo_P.
    by move=> [zb _]; apply:  (sXr _ yx1).
  set h := Lg (unionb X) id.
  have ra: fgraph h by rewrite /h; fprops.
  have rx: fgraph X by rewrite /X; fprops.
  have rb: sub (range h) (substrate r).
    by rewrite /h =>t /Lg_range_P [b bu ->]; apply: suXdr.
  have rc: (domain h) = unionb X by rewrite /h /X; aw; split;split;fprops.
  have rd: (forall l, inc l (domain X) -> has_sup_graph r (restr h (Vg X l))).
     move => l ld; apply Exercise4_7i => //.
     have re: fgraph (restr h (Vg X l)) by fprops.
     have svd: sub (Vg X l) (domain h) by rewrite /h; aw => t tv; union_tac.
     move => t /(range_gP re); aw; move=>  [z ze ->].
     have zu: inc z (unionb X) by union_tac.
     by rewrite restr_ev // /h LgV//;apply: suXdr.
  have re: has_sup_graph r h by apply Exercise4_7i => //.
  move: (sup_A2 or ra rb rc rd) => [_ xx]; move: (xx re).
  rewrite /sup_graph /h -/X Lg_range Lg_range.
  have -> : (fun_image (unionb X) id) = (unionb X).
     set_extens t; first by by move /funI_P => [a au ->]. 
     move => tu; apply /funI_P; ex_tac. 
  move => ->.
  have ww: forall l, inc l X1 -> 
    range (restr (Lg (unionb X) id) (Vg X l)) =  (Fo l x).
     move => l lx1; rewrite {2}/X; aw.
     have qa: fgraph (restr (Lg (unionb X) id) (Fo l x)) by fprops.
     have qb: sub (Fo l x) (domain (Lg (unionb X) id)).
        aw; rewrite /X => s sf; apply /setUb_P; aw; ex_tac; rewrite LgV//.
     move: (qb); aw => qc; rewrite LgV//.
     set_extens t. 
       by move /(range_gP qa); aw;move => [u uF ->]; rewrite ! LgV//; apply: qc.
     by move => tf; apply/(range_gP qa); aw; ex_tac; rewrite !LgV//; apply: qc.
  move => xv; rewrite {1} xv.
  rewrite {1} /X; aw;  congr (supremum r).
  by apply: fun_image_exten => t tx; rewrite (ww _ tx).
have sxp2: forall x, inc x (substrate r) ->
     x = supremum r (fun_image X1 (fun i => (fo i x))).
   move => x xsr; rewrite {1} (sxp1 _ xsr); congr (supremum r). 
   apply: fun_image_exten => i iX.
   symmetry; apply: (supremum_pr2 or).
   move: (For _ x iX) => sr1.
   move: (fop _ _ iX xsr) => []; rewrite (iorder_sr or sr1) => ra rb.
   apply /(lubP or sr1); split.
   split; [ apply: (sr1 _ ra) |move => y yf; exact: (iorder_gle1 (rb _ yf)) ].
   move => z [z1 z2]; exact: (z2 _ ra).
have bla: lf_axiom fp (substrate r) A.
  by move => t tsr; apply /funI_P; ex_tac.
set f := Lf fp (substrate r) A.
have bf: bijection f.
   apply: lf_bijective; [ exact | | by move => y /funI_P].
   move => u v usr vsr suv.
   rewrite (sxp2 _ usr) (sxp2 _ vsr); congr (supremum r _).
   apply: fun_image_exten => t tx.
   by move: (f_equal (Vg^~t) suv); rewrite /fp !LgV//.
have c3: cardinal (domain g) = n by rewrite /g; aw. 
have sxp3: forall x, inc x (substrate r) ->
   sub (fun_image X1 (fo^~ x)) (substrate r).
  move => x xsr t=> /funI_P [z z1 ->].
  move: (fop _ _ z1 xsr) => [h _]; move: h.
  move: (For _ x z1) => h; rewrite iorder_sr //; apply: h.
have c6: order_isomorphism f r (induced_order (order_product g) A).
  hnf; rewrite /f/bijection_prop /fiso_prop  lf_source lf_target.
  move: (iorder_osr ppa c4) => [pa' pb'].
  split => //.
  move => x y xsr ysr; move: (bla _ xsr) (bla _ ysr) => f1a f2a.
  have f3a: inc (fp x) (prod_of_substrates g) by move: (c4 _ f1a); ue. 
  have f4a: inc (fp y) (prod_of_substrates g) by move: (c4 _ f2a); ue.
  rewrite ! LfV//; split.
    move => lexp; apply /iorder_gle0P => //;apply /(order_product_gleP);split => //.
    move => i; rewrite {1}/g; aw => iX.
    move: (fop _ _ iX xsr) => []; rewrite (iorder_sr or (For _ _ iX)).
    move: (fop _ _ iX ysr) => []; rewrite (iorder_sr or (For _ _ iX)).
    move => qa qb qc qd.
    have qe: inc (fo i x) (Xf i) by move: qc => /Zo_P [].
    have qf: inc (fo i y) (Xf i) by move: qa =>  /Zo_P [].
    rewrite /g /fp ! LgV//.
    have xx: inc (fo i x) (Fo i y).
       apply: Zo_i => //; move: qc => /Zo_P [_ le1]; order_tac.
    apply /iorder_gle0P => //; exact: (iorder_gle1 (qb _ xx)).
   aw => le1; move: (iorder_gle1 le1) => /(order_product_gleP)  [_ _ ale].
  have ale1: forall i, inc i X1 -> gle r (fo i x) y.
    move: ale; rewrite /g;  aw => ale.
    move => i iX; move: (ale _ iX); rewrite LgV // /fp !LgV//  => xx.
    move: (fop _ _ iX ysr) => []; rewrite (iorder_sr or (For _ _ iX)) =>/Zo_P.
    move:(iorder_gle1 xx) => le1' [_ le2] _. order_tac.
    rewrite (sxp2 _ xsr); move: (sxp3 _ xsr) => Xsr.
    move: (Exercise4_7i lr fsr nesr Xsr) => hsX.
  move: (supremum_pr1 or hsX) => /(lubP or Xsr)  [_]. 
  apply; split; first by exact.
  by move => t /funI_P [z zi ->]; apply: ale1.
(** It suffices to show that [A] is a sublattice *)
have allg: (forall i, inc i (domain g) -> lattice (Vg g i)). 
  move => i idg; move: (c2 _ idg);apply: total_order_lattice.
exists g, A, f; simpl; split => //; split => //.
move => x y xA yA.
move: xA yA (c4 _ xA) (c4 _ yA).
move /funI_P => [x1 xsr ->] /funI_P [y1 ysr ->].
move => x2sr y2sr.
move: (setX_lattice_sup c1 allg x2sr y2sr); rewrite -/r'.
set sxy2 := sup _ _ _; set ixy2 := inf _ _ _.
move => [sxy2s ixy2s sxy2p ixy2p].
have dgX: domain g = X1 by rewrite /g; aw.
have srp: forall t, inc t (substrate r') ->  (fgraph t /\ domain t = domain g).
  move => t;rewrite ppb /prod_of_substrates /fam_of_substrates.
  have sa: fgraph (Lg (domain g) (fun i => substrate (Vg i g))) by fprops.
  move /setXb_P => [sb -> _]; saw.
move: (Exercise4_7o lr xsr ysr) => Sinf.
move: (lattice_sup_pr lr xsr ysr) (lattice_inf_pr lr xsr ysr).
set sxy := sup r x1 y1; set ixy:= inf r x1 y1. 
move => [qa qb qc][qd qe qf].
have sxyr: inc sxy (substrate r) by order_tac.
have ixyr: inc ixy (substrate r) by order_tac.
suff: fp sxy = sxy2 /\ fp ixy  = ixy2.
   move => [<- <-]; split; apply /funI_P; [by exists sxy| by exists ixy].
move: (proj1 (distributive_lattice_prop1 lr) dlr) => dlr3.
split.
  move: (srp _ sxy2s) (srp _ (c4 _ (bla _ sxyr))) => [fg1 d1] [fg2 d2].
  apply: fgraph_exten => //; rewrite d2; first by symmetry.
  red; move => i idg;rewrite (sxy2p _ idg);move: (c2 _ idg); rewrite dgX in idg.
  rewrite /fp !LgV// => toi.
  have fop1: forall t, inc t (substrate r) -> 
     (inc (fo i t) (Fo i t) /\ forall u, inc u (Fo i t) -> gle r u (fo i t)).
    move => t tsr; move: (fop _ _ idg tsr) => [].
    rewrite (iorder_sr or (For _ t idg)) => t1 t2; split; first by exact.
    by move => u uF; move: (iorder_gle1 (t2 _ uF)).
  move: (fop1 _ xsr) (fop1 _ ysr) (fop1 _ sxyr).
  move => [v1 v2][v3 v4][v5 v6].
  have sr1: inc (fo i x1) (substrate (Vg g i)) by apply: (Fos _ x1 idg _ v1).
  have sr2: inc (fo i y1) (substrate (Vg g i)) by apply: (Fos _ y1 idg _ v3).
  move: v1 => /Zo_P [v11 v12].
  move: v3 => /Zo_P [v31 v32].
  have le1 : gle r (fo i x1) (fo i sxy).
    apply: v6; apply: Zo_i => //; order_tac.
  have le2 : gle r (fo i y1) (fo i sxy).
    apply: v6; apply: Zo_i => //; order_tac.
  move: v5 => /Zo_P [v51 v52].
  have : inc (fo i sxy) (irreds r). 
     have pi: sub P  (irreds r) by apply: sub_setC.
     move: v51; case /setU1_P.
       move => fi; apply: pi; move: pX1 => [[<- _]_ ]; union_tac.
     move => ->; by apply: (Exercise4_7d).
  move  /Zo_P => [_ foi].
  move: (Exercise4_8a lr dlr3 foi xsr ysr v52).
  case => lea.
    have leb: inc (fo i sxy) (Fo i x1) by apply: Zo_i.
    move: (v2 _ leb) => lec.
    have led: (fo i sxy) = (fo i x1) by order_tac.
    rewrite led ;rewrite led in le2.
    rewrite sup_C (sup_comparable1 (proj1 toi)) //.
    by  apply/iorder_gleP.
  have leb: inc (fo i sxy) (Fo i y1) by apply: Zo_i.
  move: (v4 _ leb) => lec.
  have led: (fo i sxy) = (fo i y1) by order_tac.
  rewrite led ;rewrite led in le1.
  rewrite  (sup_comparable1 (proj1 toi)) //.
  by apply/iorder_gleP.
move: (srp _ ixy2s) (srp _ (c4 _ (bla _ ixyr))) => [fg1 d1] [fg2 d2].
apply: fgraph_exten => //; rewrite d2; first by symmetry.
red;move => i idg; rewrite (ixy2p _ idg); move: (c2 _ idg); rewrite dgX in idg.
rewrite /fp ! LgV// => toi.
have fop1: forall t, inc t (substrate r) -> 
     (inc (fo i t) (Fo i t) /\ forall u, inc u (Fo i t) -> gle r u (fo i t)).
    move => t tsr; move: (fop _ _ idg tsr) => [].
    rewrite (iorder_sr or (For _ t idg)) => t1 t2; split; first by exact.
    by move => u uF; move: (iorder_gle1 (t2 _ uF)).
move: (fop1 _ xsr) (fop1 _ ysr) (fop1 _ ixyr).
move => [v1 v2][v3 v4][v5 v6].
have sr1: inc (fo i x1) (substrate (Vg g i)) by apply: (Fos _ x1 idg _ v1).
have sr2: inc (fo i y1) (substrate (Vg g i)) by apply: (Fos _ y1 idg _ v3).
move: v1 =>/Zo_P [v11 v12].
move: v3 => /Zo_P [v31 v32].
move: v5 => /Zo_P [v51 v52].
move: toi=> [too].
have ss:  sub (Xf i) (substrate r) by apply: sXr.
rewrite iorder_sr // => tot.
have le1 : gle r (fo i ixy) (fo i x1) by apply: v2; apply: Zo_i => //;order_tac.
have le2 : gle r (fo i ixy) (fo i y1) by apply: v4; apply: Zo_i => //;order_tac.
have sr11 : inc (fo i x1) (Xf i)by move: sr1; rewrite /g LgV//.
have sr22 : inc (fo i y1) (Xf i)by move: sr2; rewrite /g LgV//.
case: (tot _ _ sr11 sr22) => le3.
  rewrite (inf_comparable1 too le3).  
  move: (iorder_gle1 le3) => le4.
  have le5: gle r (fo i x1) y1 by order_tac.
  move: (qf _ v12 le5) => l6.
  have l7: gle r (fo i x1) (fo i ixy) by apply: v6; apply: Zo_i => //.
  order_tac.
rewrite inf_C (inf_comparable1 too le3).  
move: (iorder_gle1 le3) => le4.
have le5: gle r (fo i y1) x1 by order_tac.
move: (qf _ le5 v32) => l6.
have l7: gle r (fo i y1) (fo i ixy) by apply: v6; apply: Zo_i => //.
order_tac.
Qed.

(** ---- Exercise 4.10. Let [ Ex4_10_hyp r n] be [r] is isomorphic to a
product of [n] totally ordered sets; let [ Ex4_10_conc r n] be
[r] is the intersection of [n] total orders. We show that these are equivalent,
and give two examples. *)

Definition Ex4_10_hyp r n:= 
   exists g A f,
     [/\ order_fam g, (allf g total_order), cardinal (domain g) = n ,
     sub A (substrate (order_product g)) &
     order_isomorphism f r (induced_order (order_product g) A)].
Definition Ex4_10_conc r n :=
   exists g, [/\ order_fam g, (allf g total_order), cardinal (domain g) = n ,
   (forall i, inc i (domain g) -> substrate (Vg g i) = substrate r) &
   r = intersectionb g].

(** We show here that [i => (i +c k) %%c n) ] is a permutation
of the set of integers [< n] *)

Definition shift_mod_n n k :=
   Lf (fun i => ((i +c k) %%c n)) (Nint n)(Nint n).

Lemma shift_mod_n_ax n k:
 natp n -> n <> \0c -> natp k -> 
 forall i, inc i (Nint n) -> inc ((i +c k) %%c n) (Nint n).
Proof.
move => nN nz kB i /(NintP nN) => iin; apply  /(NintP nN).
apply: crem_pr => //; apply: NS_sum => //.
apply: (NS_le_nat (proj1 iin) nN).
Qed.

Lemma shift_mod_n_vl n k i:
  natp n  -> n <> \0c -> k <c n ->  i<c n ->
  ((i +c k) %%c n) = Yo (i +c k <c n) (i +c k) ((i +c k) -c n).
Proof.
move => nN nz kn iin.
move: (NS_le_nat (proj1 kn) nN) => kN.
move: (NS_le_nat (proj1 iin) nN) => iN.
move: (NS_sum iN kN) => sN.
case: (cleT_el (CS_nat nN) (CS_nat sN)) => le1.
  move: (cdiff_pr le1) => aux.
  move: (NS_diff n sN) => dN.
  have h: cdivision_prop (i +c k) n \1c ((i +c k) -c n).
     split; first by rewrite (cprod1r (CS_nat nN)).
   apply : (csum_lt2l nN dN nN).
   rewrite aux; exact (csum_Mlelt nN (proj1 iin) kn).
   by rewrite (Y_false (cleNgt le1))  - (proj2 (cquorem_pr sN nN NS1 dN h)).
have h: cdivision_prop (i +c k) n \0c (i +c k).
  by split => //; rewrite cprod0r csum0l; fprops.
by Ytac0; rewrite  -(proj2 (cquorem_pr sN nN NS0 sN h)).
Qed.


Lemma shift_mod_n_fb n k:
  natp n  -> n <> \0c -> k <c n -> 
  bijection (shift_mod_n n k).
Proof.
move => nN nz kn. 
move: (NS_le_nat (proj1 kn) nN) => kN.
apply: lf_bijective.
  by apply: shift_mod_n_ax.
move => u v /(NintP nN) un  /(NintP nN) vn.
  rewrite (shift_mod_n_vl nN nz kn un).
  rewrite (shift_mod_n_vl nN nz kn vn) => le0.
  move: (NS_le_nat (proj1 un) nN) => uN.
  move: (NS_le_nat (proj1 vn) nN) => vN.
  apply: (csum_eq2r kN uN vN).
  move: (NS_sum uN kN) (NS_sum vN kN) => suN svN.
  move: (cleT_el (CS_nat nN) (CS_nat svN)) => cs.
  move: le0.
  case: (cleT_el (CS_nat nN) (CS_nat suN)) => le1.
    rewrite (Y_false (cleNgt le1)).
    case: cs => le2.
      rewrite (Y_false (cleNgt le2)) => eq1.
      move: (f_equal (csum2 n) eq1).
      by rewrite (cdiff_pr le1) (cdiff_pr le2).
    Ytac0 => eq1; move: (f_equal (csum2 n) eq1).
    rewrite (cdiff_pr le1) csumA => le3.
    move: (Nsum_M0le v nN).
    by rewrite -(csum_eq2r kN uN (NS_sum nN vN) le3) => /(cltNge un).
  Ytac0; case: cs => le2; last by Ytac0.
  rewrite (Y_false (cleNgt le2)) => eq1.
  move: (f_equal (csum2 n) eq1); rewrite (cdiff_pr le2) csumA => le3.
  move: (Nsum_M0le u nN); symmetry in le3.
  by rewrite -(csum_eq2r kN vN (NS_sum nN uN) le3)  => /(cltNge vn).
move => y  /(NintP nN) yn.
  move: (NS_le_nat (proj1 yn) nN) => yN.
  move:(Nsum_Mle0 y nN) => le2.
  case: (cleT_el (CS_nat kN) (CS_nat yN)) => le1.
    move: (cdiff_pr le1) => qa.
    have lt1:= (cle_ltT (cdiff_ab_le_a k (CS_nat yN)) yn).
    exists (y -c k); first by apply /(NintP nN).
    by rewrite (shift_mod_n_vl nN nz kn lt1) csumC qa; Ytac0.
  have kyn:= cleT (proj1 kn) le2.
  move: (cdiff_pr kyn) => eq1.
  move: (NS_diff k (NS_sum yN nN)) => dN.
  have lt1: (y +c n) -c k <c n. 
    apply : (csum_lt2l kN dN nN); rewrite eq1.
    by apply: csum_Mlteq.
  exists ((y +c n) -c k); first by apply /(NintP nN).
  rewrite (shift_mod_n_vl nN nz kn lt1).
  by rewrite csumC in eq1; rewrite eq1 (Y_false (cleNgt le2)) cdiff_pr1.
Qed.

Lemma Exercise4_10a r n: 
   order r -> inc n Nat -> n <> \0c -> Ex4_10_hyp r n ->  Ex4_10_conc r n.
Proof.
move => or nN nnz [g [A [f [ofg alt cdg saf isf]]]].
(** We have a family of total orders, indexed by [I] which is equipotent to
[J], the set of integers [<n]. For each [k], [shift_mod_n] give a
well-orderings on [I], thus a total ordering on the lex product of the family
*)
have [h [bh sh th]]: 
   exists h, bijection_prop h (Nint n) (domain g).
  by apply /card_eqP; rewrite (card_Nint nN) cdg.
move: (Nintco_wor n) => [].
set rI := Nint_co n; move => worI srI.
pose hk k :=  (h \co shift_mod_n n k).
have bcs: forall k, k<c n -> substrate rI = source (hk k).
  by move => k kn; rewrite /hk /shift_mod_n; aw.
have bcp: forall k, k<c n -> (h \coP shift_mod_n n k /\ bijection (hk k)).
  move => k kn.
  move: (shift_mod_n_fb nN nnz kn) => bs.
  have pa: h \coP shift_mod_n n k.
     by split => //; try fct_tac; rewrite /shift_mod_n; aw.
  by split => //; apply: compose_fb.
pose ork k := Vfs (ext_to_prod (hk k) (hk k)) rI.
have orkp: forall k, k<c n ->
   [/\ substrate (ork k) = domain g,
    order_isomorphism (hk k) rI (ork k) &
    worder (ork k)].
   move => k kn.
   have aux := (conj (proj1 worI) (bcs _ kn)).
   move: (order_transportation (proj2 (bcp _ kn)) aux).
   rewrite -/(ork k) => is1; split => //.
      by  move: (is1)  => [_ _[_ _ <-] _]; rewrite  {1} /hk; aw.
   by apply: (worder_invariance _ worI); exists (hk k).
pose opk k := order_prod (ork k) g.
have opk_ax: forall k, k <c n -> orprod_ax (ork k) g.
  by move => k kn; move: (orkp _ kn) => [sr _ wo].
have opk_total: forall k, k <c n -> total_order (opk k).
   move => k kn;move: (opk_ax _ kn) => ax;  apply: orprod_total=> //. 
(** The ordering on the product [F] is the intersection of these [n]
   total orderings. *)
set F := substrate (order_product g).
move: (order_product_osr ofg) => [pa pb].
have opksr: forall k, k<c n -> substrate (opk k) = F.
  move => k kn; move: (opk_ax _ kn) => ax.
  rewrite /opk /F orprod_sr // pb //.
have oplc1: forall k, k <c n -> sub  (order_product g) (opk k).
  move => k kn t t1.
  move:pa => [kg _ _ _].
  move: (kg _ t1) => pt; move: t1; rewrite - pt.
  set x := P t; set y:= Q t.
  move /order_product_gleP=> [xp yp lexy];apply /(orprod_gle1P (opk_ax _ kn)).
  move: (orkp _ kn) => [srd _ [ok _]].
  have sa: sub (Zo (domain g) (fun i => Vg x i <> Vg y i)) (substrate (ork k)).
    rewrite srd; apply: Zo_S.
  split => //; move => j []; rewrite (iorder_sr ok sa).
  move /Zo_P =>[s1 s2]; split => //; by apply: lexy.
have lt0n: \0c <c n by apply /strict_pos_P1.
have zi: inc \0c  (Nint n)  by apply /NintP.
have ne1: nonempty (Lg (Nint n) opk).
  by exists (J \0c  (opk \0c)); apply /funI_P; exists \0c.
have conc1: (order_product g) = intersectionb (Lg (Nint n) opk).
  set_extens t.
    move => tg; apply /(setIb_P ne1); aw => i ib; rewrite LgV//.  
   by move/(NintP nN): ib => lin; apply (oplc1 _ lin).
  move /(setIb_P ne1); aw => h1; move: (h1 _ zi); rewrite LgV// => tz.
  move: (opk_total _ lt0n) => [[gr0 _] _].
  move: (gr0 _ tz); rewrite /pairp; set x := P t; set y:= Q t => eq1.
  have pa': forall i, i <c n -> gle (opk i) x y.
    move => i lin.
    have lic: inc i (Nint n) by apply /(NintP nN).
    move: (h1 _ lic); rewrite - eq1;rewrite LgV//.
  move: (pa' _ lt0n) =>  /(orprod_gleP (opk_ax _ lt0n)) [xsr ysr _ _ _].
  rewrite - eq1; apply /order_product_gleP;split => //; move => i idg.
  have pc: gle (Vg g i) (Vg x i) (Vg x i).
    move: xsr => /prod_of_substratesP [fgx dx hx]. 
    move: (hx _ idg) (ofg _ idg) => xsr1 odg. 
    by order_tac.
  move: (idg); rewrite -th  => idh.
  move: (bij_surj bh idh) => [k]; rewrite sh => /(NintP nN) kn Wk.
  move: (pa' _ kn) => /(orprod_gleP (opk_ax _ kn)) [_ _ ww]. 
  case: ww; first by move => <-.
  move => [j [jsk lta lea]].
  case: (equal_or_not i j); first by move => ->; exact (proj1 lta).
  move => ij.
  move: (orkp _ kn) => [sa [_ _ [bk sk tk] mk] sc].
  rewrite - tk in jsk.
  move: (bij_surj bk jsk) => [ja jas jav].
  have zl1: gle rI \0c ja.
     apply /(Nintco_gleP nN).
     move: jas; rewrite sk  srI; move /(NintP nN)=> jn;split => //.
     apply: (cle0x (proj31_1 jn)).
  hnf in mk;rewrite sk srI in mk jas.
  move: (proj1 (bcp _ kn)) => cop.
  have zs1:inc \0c (source (shift_mod_n n k)) by rewrite /shift_mod_n; aw.
  move: (mk _ _ zi jas); rewrite - jav /hk; rewrite compfV//.
  move: (shift_mod_n_ax nN nnz (NS_le_nat (proj1 kn) nN)) => ta.
  rewrite /shift_mod_n (LfV ta zi) (shift_mod_n_vl nN nnz kn lt0n).
  have ck := proj31_1 kn.
  rewrite csum0l//; Ytac0; move => eqv; move: (proj1 eqv zl1).
  by rewrite -Wk => aux; rewrite - (lea _ (conj aux ij)).
(** We restrict our orderings to [A] *)
pose opkA k := induced_order (opk k) A.
have altA: forall k, k <c n -> (total_order (opkA k)).
   move => k kn; move: (opk_total _ kn) => to1.
   by apply: total_order_sub => //; rewrite (opksr _ kn).
have opkAi: (induced_order (order_product g) A) 
    = intersectionb (Lg (Nint n) opkA).
  rewrite /opkA /induced_order conc1.
  have ne2:nonempty (Lg (Nint n) (fun k => opk k \cap coarse A)).
    by exists (J \0c((opk \0c) \cap coarse A)); apply /funI_P; exists \0c. 
  move :(setIb_P ne2) (setIb_P ne1); aw => ia ib.
  set_extens t. 
    move => /setI2_P [ta tb]; apply /ia => i id; rewrite LgV//.
    by apply /setI2_P;split => //; move /ib: ta; aw => k; move: (k _ id); rewrite LgV//.
  move => pa'; apply /setI2_P;  move /ia: pa' => k; split.
    by apply/ib => i id;rewrite LgV//; move: (k _ id); rewrite LgV// => /setI2_P [].
  by move: (k _ zi); rewrite LgV// => /setI2_P [].
(** It suffices to transport the orderings via the inverse of [f] *)
move: (isf) => [_ _ [bf _ _]_].
move: (inverse_bij_fb bf) => bif.
set ibf := (inverse_fun f).
pose orkE k := Vfs (ext_to_prod ibf ibf) (opkA k).
have qa: order (order_product g) by apply (proj1 (order_product_osr ofg)).
move: (iorder_osr qa saf) => [qb qb'].
have qc: A = target f.
  by move: isf => [_ _ [_ _ tf] _ ]; rewrite tf qb'.
have qd: substrate (induced_order (order_product g) A) = source ibf.
  by rewrite iorder_sr //; rewrite /ibf; aw.
set orkEi := Vfs (ext_to_prod ibf ibf) 
    (induced_order (order_product g) A).
have orkEip:  order_isomorphism ibf (induced_order (order_product g) A) orkEi.
  by apply: order_transportation.
have eq0: orkEi = r.
  move: orkEip => [o1 o2 [bk sk tk] mk].
  move: isf => [_ _ [_ sf tf] mf].
  have tibf: target ibf = source f by rewrite /ibf; aw.
  have sibf: source ibf = target f by rewrite /ibf; aw.
  hnf in mk; rewrite sibf in mk.
  have ffi: forall z, inc z (source f) -> 
      (inc (Vf f z) (target f) /\ Vf ibf (Vf f z) = z).
      move => e zf;split; [  Wtac; fct_tac | by rewrite inverse_V2].
  apply: order_exten => // => x y; split => cp1.
     have xs: inc x (substrate orkEi) by order_tac.
     have ys: inc y (substrate orkEi) by order_tac.
     rewrite - tk tibf in xs ys.  
     move: (ffi _ xs) (ffi _ ys) => [pa' pb'] [pc pd].
     by rewrite (mf _ _ xs ys) (mk _ _ pa' pc) pb' pd.
  have xs: inc x (substrate r) by order_tac.
  have ys: inc y (substrate r) by order_tac.
  rewrite - sf in xs ys.
  move: (ffi _ xs) (ffi _ ys) => [pa' pb'] [pc pd].
  by move: cp1; rewrite (mf _ _ xs ys) (mk _ _ pa' pc) pb' pd.
have orkEp: forall k, k<c n ->
  [/\ substrate (orkE k) = substrate r,
    order_isomorphism ibf (opkA k) (orkE k) &
    total_order (orkE k)].
   move => k kn.
   move: (altA _ kn) => tor; move: (tor) => [ok _].
   move: (opk_total _ kn) (opksr _ kn) => [orkn _] srkn.
   have srk: substrate (opkA k) = source ibf.
     by rewrite /ibf; aw;rewrite -qc /opkA iorder_sr // srkn.
  move: (order_transportation bif (conj ok srk)).
  rewrite -/ibf -/(orkE k) => ois.
  move: (ois) => [_ o2 [bk sk tk] mk].  
  have sr1: substrate (orkE k) = substrate r. 
        by rewrite - tk /ibf; aw; move: isf => [_ _ [_ <- _]_].
  split => //; split; [ exact | move => x y xsr ysr].
  rewrite - tk in xsr ysr. 
  move: (bij_surj bk xsr) => [x' x's ->].
  move: (bij_surj bk ysr) => [y' y's ->].
  move: tor => [_]; rewrite - sk => tor.
  by case: (tor _ _ x's y's); rewrite mk // => cp1; [left | right].
set G := Lg (Nint n) orkE.
have c0: forall i, inc i (domain G) ->
  [/\ order (Vg G i), total_order (Vg G i) &substrate (Vg G i) = substrate r].
  rewrite /G; aw => i idg; rewrite LgV//; move: idg => /(NintP nN) idg.
  by move: (orkEp _ idg) => [ta [_ tb]];split => //; move: tb => [].
have c1: order_fam G  by move => i idg; move: (c0 _ idg) => [ok _].
have c2:  (allf G total_order) by move => i idg; move: (c0 _ idg) => [_ ok _ ].
have c3: cardinal (domain G) = n by rewrite /G; aw; rewrite card_Nint.
have c4: forall i, inc i (domain G) -> substrate (Vg G i) = substrate r.
  by move => i idg; move: (c0 _ idg) => [_ _ ok  ].
exists G;split => //.
rewrite -eq0 /orkEi opkAi /G /orkE.
have fif: injection ibf by move: bif => [].
move: (ext_to_prod_fi fif fif); set hf := (ext_to_prod ibf ibf) => fh.
rewrite /intersectionb  (inj_image_setIf _ _ fh).
have ne2: nonempty (Nint n) by exists \0c; aw.
 aw; set_extens t; move => /(setIt_P _ ne2) hp;
    apply /(setIt_P _ ne2) => j; move: (R_inc j) => ri; move: (hp j); rewrite !LgV//. 
Qed.


(** Converse is easy *)

Lemma Exercise4_10b r n: 
  order r -> natp n -> n <> \0c -> Ex4_10_conc r n -> Ex4_10_hyp r n.
Proof.
move => or nN nz [g [og altg cdg ssr rb]].
case: (emptyset_dichot (domain g)) => nedg.
  by case: nz; rewrite - cdg nedg cardinal_set0.
set E := substrate r.
pose f := cst_graph (domain g).
set A := fun_image E f.
set ff:= Lf f E A.
have ta: lf_axiom f E A by rewrite /A;move => t tdg; apply /funI_P; ex_tac.
have bf: bijection ff.
  apply: lf_bijective => //.
    move => u v udg vdg sv.
    move: (nedg) => [k kdg]; move: (f_equal (Vg^~ k) sv).
    rewrite /f/cst_graph ! LgV//.
  by move => y /funI_P.
move:(order_product_osr og) => [or1 sr1].
have srA: sub A (substrate (order_product g)).
   have aux: fgraph (fam_of_substrates g) by rewrite /fam_of_substrates; fprops.
  rewrite sr1.
  move => t /funI_P [z zi ->]; rewrite /f/cst_graph; aw.
  apply /prod_of_substratesP;split;aww. 
  by move => i idg; rewrite LgV//; rewrite ssr.
exists g, A, ff;split => //.
move: (iorder_osr or1 srA) => [pa' pb'].
rewrite /ff; split => //; first by  rewrite pb'; saw.
hnf; aw;move => x y xE yE.
move: srA ;rewrite sr1 => srA.
move:(ta _ xE) (ta _ yE) => xA yA.
move: (srA _ xA) (srA _ yA) => fxA fyA; rewrite !LfV//.
split.
  move => le1; apply /iorder_gle0P => //;apply /order_product_gleP; split => //. 
  move => i idg; rewrite /f/cst_graph !LgV//.
  move: le1; rewrite /gle/related rb => le1.
  exact: (setIb_hi le1 idg).
move => h; move :(iorder_gle1 h); move /order_product_gleP => [_ _ ali].
rewrite /gle/related rb; apply: setIb_i.
  case: (emptyset_dichot (domain g)) => neg.
    by case: nz; rewrite - cdg neg cardinal_set0.
  by apply /domain_set0P. 
move => i idg; move: (ali _ idg); rewrite /f/cst_graph !LgV//.
Qed.

(** Let's say that [r1] and [r2] are orthogonal if they have the same substrate
and if any pair of two distinct elements are comparable by exactly one of 
the two orderings.

In this case, the union [r3] is a total ordering.
If we replace [r2] by its opposite 
we get [r4], and [r1] is the intersection of [r3] and [r4] *)

Definition orthogonal_order r r' := 
   forall x y, inc x (substrate r) -> inc y (substrate r) -> x <> y ->
   exactly_one (ocomparable r x y) (ocomparable r' x y).

Lemma orthogonal_union_order r r':
   order r -> order r' -> substrate r = substrate r' -> orthogonal_order r r' ->
   (total_order (r \cup r') /\ substrate (r \cup r') = substrate r).
Proof.
move => or or' ss otr; set r'' := r \cup r'.
have gu: sgraph r'' by apply: setU2_graph; fprops.
have sr1: substrate r'' = substrate r.
  set_extens t. 
     move /(substrate_P gu).
    case; case => [y];case /setU2_P => h; try substr_tac;rewrite ss; substr_tac.
  move => tsr; apply /(substrate_P gu);left.
  by exists t; apply /setU2_P; left; order_tac.
suff ors: order (r \cup r').
  split => //; split; first by exact.
  rewrite sr1 => x y xsr ysr; case: (equal_or_not x y) => exy.
     rewrite -exy; left; order_tac; ue.
  move: (otr _ _ xsr ysr exy) => [h _].
  rewrite/ocomparable /gle /related /r''; aw; case:h; case => cxy; 
   try (solve [left; fprops]); right; fprops.
split => //.
    by hnf;rewrite sr1 => y ysr; apply /setU2_P;left; order_tac.
  move => y x z; case /setU2_P  => le1; case /setU2_P => le2; apply /setU2_P.
  - left; order_tac.
  - have xsr: inc x (substrate r) by substr_tac.
    have ysr: inc y (substrate r) by substr_tac.
    have zsr: inc z (substrate r) by rewrite ss; substr_tac.
    case: (equal_or_not x z) => exz; first by rewrite exz; left; order_tac.
    move: (otr _ _ xsr zsr exz) => [h1 _].
    case: h1; case => cxz; try (by left); try (by right).
      case: (equal_or_not z y) => zy; first by rewrite zy; left.
           move: (otr _ _ zsr ysr zy) => [_]; case;split; last by right.
          left; move: cxz; rewrite /gle/related => cxz; order_tac.
      case: (equal_or_not x y) => yx; first by rewrite yx; right.
        move: (otr _ _ xsr ysr yx) => [_]; case; split; first by left.
        right; move: cxz; rewrite /gle/related => cxz; order_tac.
  - have xsr: inc x (substrate r) by rewrite ss; substr_tac.
    have ysr: inc y (substrate r) by rewrite ss; substr_tac.
    have zsr: inc z (substrate r) by substr_tac.
    case: (equal_or_not x z) => exz; first by rewrite exz; left; order_tac.
    move: (otr _ _ xsr zsr exz) => [h1 _].
    case: h1; case => cx; try (by left); try (by right).
       case: (equal_or_not x y) => xy; first by rewrite xy; left.
         move: (otr _ _ xsr ysr xy) => [_]; case; split;last by left.
         right; move: cx; rewrite /gle/related => cxz; order_tac.
     case: (equal_or_not z y) => zx; first by rewrite zx; right.
       move: (otr _ _ zsr ysr zx) => [_]; case; split;first by right.
       left; move: cx; rewrite /gle/related => cxz; order_tac.
  - right; order_tac.
move => x y; case /setU2_P => le1; case /setU2_P=> le2; try order_tac.
  ex_middle xney.
    have xsr: inc x (substrate r) by substr_tac.
    have ysr: inc y (substrate r) by substr_tac.
    have pa: ocomparable r x y by left.
    have pb: ocomparable r' x y by right.
    by move: (otr _ _ xsr ysr xney) => [_]; case.
 ex_middle xney.
    have xsr: inc x (substrate r) by substr_tac.
    have ysr: inc y (substrate r) by substr_tac.
    have pa: ocomparable r x y by right.
    have pb: ocomparable r' x y by left.
    by move: (otr _ _ xsr ysr xney) => [_]; case.
Qed.

Lemma orthogonal_union_inter r r' 
   (r1 := r \cup r') (r2 := r \cup opp_order r'):
   order r -> order r' -> substrate r = substrate r' -> orthogonal_order r r' ->
   [/\ total_order r1, total_order r2,
    substrate r1 = substrate r, substrate r2 = substrate r & r = r1 \cap r2].
Proof.
move => or or' ssr ort1.
move: (opp_osr or') => [or'' sr''].
rewrite - ssr in sr''.
have cc: forall x y, ocomparable r' x y <-> ocomparable (opp_order r') x y.
   move => x y; split. 
     by case => pa; [right | left]; apply /opp_gleP.
   by case => pa; [right | left]; apply /opp_gleP.
have ort2: orthogonal_order r  (opp_order r').
  move => x y xsr ysr xny; move: (ort1 _ _ xsr ysr xny).
  move => [pa pb]; split.
     by case: pa => h1; [by left | right]; apply /cc.
  by move => [pc pd];case:pb; split => //; apply /cc.
symmetry in sr''.
move: (orthogonal_union_order or or' ssr ort1); rewrite -/r1; move => [pa pb].
move: (orthogonal_union_order or or'' sr'' ort2); rewrite -/r1; move => [pc pd].
split => //.
rewrite - (set_UI2r r r' (opp_order r')); symmetry; apply /setU2id_Pr.
move => t /setI2_P [ta tb].
have gr': sgraph r' by fprops.
move: (gr' _ ta); rewrite /pairp => pt.
have le1: gle r' (P t) (Q t) by rewrite /gle/related pt.
have le2: gle r' (Q t) (P t) by  apply /opp_gleP; rewrite /gle/related pt.
have eq1: P t = Q t by order_tac.
have psr: inc (P t) (substrate r) by rewrite ssr; order_tac.
by rewrite - pt -eq1; order_tac.
Qed.

(** We show that [r] is isomorphic to a subset of a product of two
totally ordered sets iff there is [r'] orthogonal to it. 
One way is immediate.
*)

Lemma Exercise4_10c r: order r -> (Ex4_10_hyp r \2c <->
  exists r', [/\ substrate r' = substrate r, order r' & orthogonal_order r r']).
Proof.
move => or; set E := substrate r.
split; last first.
  move => [r' [ssr or' orth]].
  move: (orthogonal_union_inter or or' (sym_eq ssr)  orth).
  set r1 := r \cup r'; set r2 := r \cup (opp_order r').
  move => [to1 to2 sr1 sr2 rin]; move: (to1) (to2) => [or1 _] [or2 _].
  apply: (Exercise4_10b or NS2 card2_nz).
  exists (variantLc r1 r2);split => //.
  + by hnf; aw; move => x xtp; try_lvariant xtp.
  + by hnf; aw; move => x xtp; try_lvariant xtp.
  + aw; apply: cardinal_set2; fprops.
  + by aw; move => x xtp; try_lvariant xtp.
  + by rewrite /intersectionb; aw; trivial;rewrite setIf2f; aw.
(** Assume [r] isomorphic to a subset of a product of two sets.
If [x] is in [E], let [x1] and [x2] be the two components of the image
consider [x1 <x2  /\ y2 < x2 ]. This is an ordering *)
move => [g [T [f [ofg alt cdg sar oif]]]].
move /(set_of_card_twoP): cdg => [iA [iB [niAB vcdg]]].
have siA: inc iA (domain g) by rewrite vcdg; fprops.
have siB: inc iB (domain g) by rewrite vcdg; fprops.
set rA:= Vg g iA; set rB:= Vg g iB.
have toA: total_order rA by apply: alt.
have toB: total_order rB by apply: alt.
move: (toA) (toB) => [orA _] [orB _].
pose prA x := Vg (Vf f x) iA; pose prB x := Vg (Vf f x) iB. 
pose cmp x y := x = y \/ (glt rA (prA x) (prA y) /\ (glt rB (prB y) (prB x))).
pose cmp' x y := [/\ inc x E, inc y E & cmp x y].
set r' := graph_on cmp E.
have samer: r' = graph_on cmp' E.
  by set_extens t => /Zo_P [pa pb];  
   move /setX_P: (pa) => [pd pe pf];apply /Zo_P;split => //; move : pb => [_ _].
have rr': forall x, inc x E -> cmp x x by move => x _; left.
move: (graph_on_sr rr'); rewrite -/r' => sr'.
have or': order r'.
    apply: order_from_rel; split => //.
       move => y x z pa pb.
       case: (equal_or_not y z); [ by move => <- | move => ynz].
       case: pa; [by  move => ->|  move => [la lb]].
       case: pb; first by  move => h; contradiction.  
       move => [lc ld]; right; split; order_tac.
    move => x y.
       case; [by  move => ->|  move => [la _]].
       case; [by  move => ->|  move => [lb _]].
       order_tac.
  by move => x y _; split; left.
move:(order_product_osr ofg) => [orp srp].
(** Note that [x<= y] is [x1 <= y1 /\ x2 <= y2]. If the first or second
components are the same then [x] and [y] are comparable *)
move: (oif) => [_ _ [ff sf tf] mn].
have ta: forall x, inc x (source f) -> inc (Vf f x) T.
  move: tf;rewrite (iorder_sr orp sar) => <-; move => x xsf; Wtac; fct_tac.
have spra: forall x, inc x E ->
   (inc (prA x) (substrate rA) /\ inc (prB x) (substrate rB)).
   rewrite /E - sf => x xsf; move: (sar _ (ta _ xsf)).
   rewrite srp; move /prod_of_substratesP.
   by move => [fgw dw hw]; rewrite /rA/rB /prA /prB; split; apply: hw.
have sprb: forall x y, inc x E -> inc y E ->
     gle rA (prA x) (prA y) -> gle rB (prB x) (prB y) -> gle r x y.
  rewrite /E - sf => x y xsf ysf cp1 cp2; rewrite (mn _ _ xsf ysf).
  move: (ta _ xsf) (ta _ ysf) => xa ya; apply /iorder_gle0P => //.
  move: sar; rewrite srp => sa1.
  apply /order_product_gleP;split => //; try apply:sa1 => //.
  rewrite vcdg; move => t; case  /set2_P => -> //.
have sprd: forall x y,  gle r x y ->
    (gle rA (prA x) (prA y) /\ gle rB (prB x) (prB y)).
  move => x y le1.
  have xsf: inc x (source f) by rewrite sf; order_tac.
  have ysf: inc y (source f) by rewrite sf; order_tac.
  move: le1; rewrite (mn _ _ xsf ysf) => le1.
  move: (iorder_gle1 le1) => /order_product_gleP [_ _ h].
  by split; apply: h.
have sprc: forall x y, gle r' x y <-> cmp' x y.
  by move => x y; apply: graph_on_P1.
exists r'; split => //.
move => x y xsr ysr xny; split.
  move: (spra _ xsr) (spra _ ysr) => [pa pb][pc pd].
  move:(proj2 toA _ _ pa pc);  move:(proj2 toB _ _ pb pd) => cp1 cp2.
  case: (equal_or_not (prA x) (prA y)) => neA.
    by left;case:cp1=>cp;[left | right ];apply:sprb => //;rewrite neA;order_tac.
  case: (equal_or_not (prB x) (prB y)) => neB.
    by left;case:cp2=>cp;[left | right ];apply:sprb => //;rewrite neB;order_tac.
  case: cp1; case: cp2 => l1 l2.
     by left; left; apply: sprb.
  right; right; rewrite sprc;split => //; right;split => //; split => //;fprops.
  right; left; rewrite sprc; split => //; right;split => //; split => //;fprops.
  by left;  right;  apply: sprb.
have ynx: y <> x by apply:nesym.
move => [ca cb]; case:ca => ca; move: (sprd _ _ ca) => [pa pb]; 
 case: cb; move/sprc => [_ _];case => //; move => [pc pd]; order_tac.
Qed.


(** Example. Let [E] be finite with [n] elements, 
   [F] the set of singletons and complement of singletons, ordered by inclusion. 
The least [m] satisfying the condition is [n]. *)

Lemma Exercise4_10d E n 
  (F := (fun_image E singleton) \cup (fun_image E (fun z => E -s1 z)))
  (r := sub_order F):
  natp n -> cardinal E = n ->
  ( Ex4_10_hyp r n /\ 
   forall m, natp m -> Ex4_10_hyp r m -> n <=c m).
Proof. 
move=> nN cen.
move:(sub_osr F) => [or sr].
(** The case [n= 0] is trivial *)
case: (equal_or_not n \0c) => nz.
  split; last by move=> m mb _; rewrite nz; apply: cle0n. 
  set g := Lg emptyset id.
  have pa: order_fam g 
     by rewrite /g;hnf;aw;move => t /in_set0.
  move: (order_product_osr pa) => [pb pb'].
  move: empty_function_function => [pc pd pe].
  have bef: bijection  empty_function.
    split; split => //; rewrite pd ?pe; [move => x y | move => y]; case; case.
  exists g, emptyset, empty_function; rewrite/g;saw.
        by hnf;aw;move => t /in_set0.
      by rewrite cardinal_set0.
    fprops.
  have hh: sub emptyset (substrate (order_product g)) by fprops.
  move: (iorder_osr pb hh)=> [sa sb].
  split => //.
    rewrite sb; split => //; rewrite pd sr /F.
    rewrite nz in cen; move: (card_nonempty cen) => ->.
    by rewrite funI_set0 funI_set0 setU2_id.
  by hnf; rewrite pd; move => x y /in_set0.
(** Basic properties of the orderings. *)
have pa: forall a, inc a E -> inc (singleton a) F.
  move => a ae; apply /setU2_P; left; apply /funI_P; ex_tac.
have pb: forall a, inc a E -> inc (E -s1 a) F.
  move => a ae; apply /setU2_P; right; apply /funI_P; ex_tac.
have pc: forall a b, inc a E -> inc b E -> a <> b -> 
   gle r (singleton a) (E -s1 b).
  move => a b aE bE and; apply /sub_gleP;split;fprops.
  move => t /set1_P ->; apply /setC1_P;split => //.
have pd: forall a, inc a E -> singleton a <> E -s1 a.
  by move => a ae eq; move: (set1_1 a); rewrite eq;apply /setC1_P => //; case.
(** We show first that there is a solution for [n]. *)
split.
  (** We have two injections [E -> F], the first one with image [F1].
      We define here the inverse mapping*)
  set F1:= fun_image E singleton.
  pose ra x := (union x). 
  pose rb x :=  (union (E -s x)).
  have splitF: forall x, inc x F ->
    ( [/\ inc x F1, inc (ra x) E & x = singleton (ra x)] 
     \/ [/\ inc x (F -s F1), inc  (rb x) E & x = E -s1 (rb x)]).
     move => x; rewrite /F -/F1 /ra /rb => xF.
     case: (inc_or_not x F1) => xF1.
      by left; move: (xF1) => /funI_P [z zE h]; rewrite {2 4} h !setU_1.
     right;move: (xF) => /setU2_P; case => //; move /funI_P => [z zE zv].
     set t := (E -s x). 
     have ->: t = singleton z by rewrite /t zv  setC_K // => q /set1_P ->.
     by rewrite setU_1; split => //; apply /setC_P.
  (** Let [I] be the set of integers less than [n] and [h] a bijection
      [I -> E]; by permutation [hk n] is another bijection. *)
  apply (Exercise4_10b or nN nz).
  have [h [bh sh th]]: 
   exists h, bijection_prop h (Nint n) E.
     by apply /card_eqP; rewrite card_Nint.
  move: (Nintco_wor n) => [].
  set rI := Nint_co n; move => worI srI.
  pose hk k :=  (h \co shift_mod_n n k).
  have bcs: forall k, k<c n -> substrate rI = source (hk k).
    by move => k kn; rewrite /hk /shift_mod_n; aw.
  have bcp: forall k, k<c n -> (h \coP shift_mod_n n k /\ bijection (hk k)).
    move => k kn.
    move: (shift_mod_n_fb nN nz kn) => bs.
    have qb: h \coP shift_mod_n n k.
      by  split => //; try fct_tac; rewrite /shift_mod_n; aw.
    by split => //; apply: compose_fb.
  have F1F: sub F1 F by move => t ta; apply /setU2_P; left.
  pose hi k x := Vf (inverse_fun (hk k)) x.
  have bce: forall k x, k <c n -> inc x E -> inc (hi k x) (substrate rI).
    move => k x kn xE.
    move: (bcp _ kn) => [_ bk].
    move: (inverse_bij_fb bk) =>[[fik _] _].
    have si:  source (inverse_fun (hk k)) = E by aw;  rewrite /hk; aw.
    have -> : substrate rI = target (inverse_fun (hk k)) by aw; rewrite -  bcs.
    rewrite /hi;Wtac.
  have bcf:forall k x y, k <c n -> inc x E -> inc y E ->hi k x = hi k y -> x= y.
    move => k x y kn.
    move: (bcp _ kn) => [_ bk].
    have <- : target (hk k) = E by rewrite /hk; aw.
    move => xE yE sv; move : (f_equal (fun z => Vf (hk k) z) sv).
    rewrite inverse_V // inverse_V //.
  move: (worI) => [orI _].
  move: (worder_total worI) => [_ torI].
  (** The following relation is reflexive and total *)
  pose r1 k x y :=
    [\/ [/\ inc x F1, inc y F1 & (gle rI (hi k (ra x)) (hi k (ra y)))],
     [/\ inc x F1, inc y (F -s F1) &
        (ra x <> rb y \/ (ra x = rb y /\ (hi k (ra x) <> cpred n)))],
     [/\ inc x (F -s F1), inc y F1, (rb x = ra y) &
        (hi k (ra y)) = cpred n ] |
     [/\ inc x (F -s F1), inc y (F -s F1) &
      (gle rI (hi k (rb y)) (hi k (rb x)))]].
  have dr1: forall k x y, r1 k x y -> (inc x F /\ inc y F).
     move => k x y; case.
     by move => [qa qb _]; split => //; apply: F1F.
     by move => [qa] /setC_P [yf _] _;split => //;apply: F1F.
     by move => [] /setC_P [xa _] yb _;split => //;apply: F1F.
     by move => []  /setC_P [xa _]  /setC_P [ya _] _;split => //.
  have dr2: forall k x, k <c n -> inc x F -> r1 k x x.
    move => k x kn xF.
    case: (splitF _ xF); move => [qa qb qc].
      by constructor 1; split => //; order_tac;apply: bce.
    by constructor 4; split => //; order_tac; apply: bce.
  have dr3: forall k x y, k <c n -> inc x F -> inc y F -> 
       r1 k x y \/ r1 k y x.
    move => k x y kn xF yF.
    case: (splitF _ xF) =>[] [qa qb qc]; case: (splitF _ yF)=> [] [qd qe qf].
    - move: (bce _ _ kn qb) (bce _ _ kn qe)  => sr1 sr2.
      by case: (torI _ _ sr1 sr2); [left | right ]; in_TP4.
    - case: (equal_or_not (ra x) (rb y)) => cpi.
        case: (equal_or_not (hi k (ra x)) (cpred n)) => cpj.
          right;in_TP4.
        by left; constructor 2; split => //; right.
      by left; constructor 2; split => //; left.
    - case: (equal_or_not (ra y) (rb x)) => cpi.
        case: (equal_or_not (hi k (ra y)) (cpred n)) => cpj.
          left; in_TP4.
        by right; constructor 2;split => //; right.
      by right; constructor 2;split => //; left.
    - move: (bce _ _ kn qb) (bce _ _ kn qe)  => sr1 sr2.
      by  case: (torI _ _ sr2 sr1); [left | right ]; in_TP4.
(** the relation is antisymmetric and transitive *)
   have dr4: forall k x y, k<c n -> r1 k x y -> r1 k y x -> x = y.
      move => k x y kn c1 c2.
      move: (dr1 _ _ _ c1) => [xF yF]; case: c1. 
      - move => [xF1 yF1 le1].
          have sa: inc x (F -s F1) -> False by move /setC_P => [].
          have sb: inc y (F -s F1) -> False by move /setC_P => [].
          case: (splitF _ xF); last by move => [].
          case: (splitF _ yF); last by move => [].
          move => [_ qb qc]  [_ qb' qc'].
          case: c2; [ | move => [] | move => [] | move => []] => //.
            move => [_ _ le2].
              have eq1:  (hi k (ra y)) = (hi k (ra x)) by order_tac.
              by rewrite qc qc' (bcf _ _ _ kn qb qb' eq1).
      - move => [xF1 yF1 le1].
          have sa: inc x (F -s F1) -> False by move /setC_P => [].
          move: (yF1) => /setC_P [_ sb].
          case: c2; [ move => [] | move => [] | | move => [_ ]] => //.
          move => [_ _ ta tb].
          by case: le1; rewrite ta //; move => [].
     - move => [xF1 yF1 ta tb].
          have sa: inc y (F -s F1) -> False by move => /setC_P [].
          move: (xF1); move => /setC_P [_ sb].
          case: c2; [ move => [] | | move => [] | move => [] ] => //.
         by move => [_  _]; rewrite ta;case => //; move => [].
     - move => [xF1 yF1 le1].
       move: (xF1)(yF1) =>/setC_P  [_ sa] /setC_P [_ sb].
      case: c2; [move => [] | move => [] | move =>[] | move=> [_ _ le2]] => //.
       have eq1:  (hi k (rb y)) = (hi k (rb x)) by order_tac.
       case: (splitF _ xF); first by move => [].
       case: (splitF _ yF); first by move => [].
       move => [_ qb ->]  [_ qb' ->].
       by rewrite (bcf _ _ _ kn qb qb' eq1).
  move: (cpred_pr nN nz); move=> [pnN pnv].
  have lcpnn: cpred n <c n by rewrite {2} pnv; apply: cltS.
  have QA: forall u v, gle rI u v -> u = v \/ u <c cpred n.
    move => u v le1; case: (equal_or_not u v); [by left | move => uv; right].
    move: le1 => /(Nintco_gleP nN) [luv vn].
    move: vn; rewrite {1} pnv; move / (cltSleP pnN) => tc.
    exact (clt_leT (conj luv uv) tc).
  have QB: forall u, inc u (substrate rI) -> gle rI u (cpred n).
     move => u; rewrite srI => /(NintP nN) uc. 
     apply /(Nintco_gleP nN);split => //.
     by move: uc; rewrite {1} pnv;move /(cltSleP pnN).
  have dr5: forall k x y z, k<c n -> r1 k x y -> r1 k y z -> r1 k x z.
    move => k x y z kn le1 le2.
    move: (dr1 _ _ _ le1) (dr1 _ _ _ le2) => [xF yF] [_ zF].
    case: le1.
    - move => [xF1 yF1 le1].
      have sa: inc x (F -s F1) -> False by move /setC_P => [].
      have sb: inc y (F -s F1) -> False by move /setC_P => [].
      case: (splitF _ xF); last by move => [].
      case: (splitF _ yF); last by move => [].
      move => [_ qb qc]  [_ qb' qc'].
      case: le2; move => [p1 p2 p3] => //.
          constructor 1;split => //; order_tac.
        constructor 2; split => //.
        case: (equal_or_not  (ra x) (ra y)); [ by move => -> | move => nexy].
        case: (equal_or_not (ra x) (rb z)) => eq1; last by left.
        right; case: (equal_or_not (hi k (ra x)) (cpred n)) => e2; last by done.
        case:(QA _ _ le1); first  by move => tb; move: (bcf _ _ _ kn qb' qb tb).
        by move => [_ neq].
    - move => [xF1 yF1 le1]; move: yF1 => /setC_P [_ nyF1].
      case: le2; move=> [p1 p2 p3] //.
         move => p4; constructor 1 ;split => //; rewrite p4; apply: QB.
         apply: bce => //; case: (splitF _ xF); move => [ta tb _] //.
         by move: ta => /setC_P [_ bad].
       constructor 2; split => //.
       case: (equal_or_not  (rb y) (rb z)); [ by move => <- | move => neyz].
       case: (equal_or_not (ra x) (rb z)) => eq1; last by left.
       right; case: (equal_or_not (hi k (ra x)) (cpred n)) => e2 //.
       case: (QA _ _ p3);  last by rewrite -eq1; move => [_ aux];split => //.
       move => tb; case: neyz.
       case: (splitF _ yF); [by move => [] | move =>  [_ qb' qc']].
       case: (splitF _ zF); [move => [zf1 _] | move => [_ qb qc]].
         by move: p2 => /setC_P [].
       by rewrite (bcf _ _ _ kn qb qb' tb).
   - move=> [xF1 yF1 eq1 eq2]; move: (xF1) => /setC_P [_ nxF1].
     have tc: inc y (F -s F1) -> False by move /setC_P => [].
     case: le2; move=> [p1 p2 p3] //.
       case: (QA _ _ p3); last by move => [_].
       case: (splitF _ yF); last by  move => [].
       case: (splitF _ zF); last by  move => [bad _]; move: bad => /setC_P [].
       move =>  [_ qb qc] [_ qb' qc'] tb.
       move: (bcf _ _ _ kn qb' qb tb) => sra.
       constructor 3;split => //; ue.
     constructor 4; split => //.
     rewrite eq1 eq2;apply: QB; apply: bce => //.
     case: (splitF _ zF); last by  move => [_ ok _].
     by move: p2 => /setC_P [_ qa]  [qb _].
    - move => [xF1 yF1 le1].  
      have sa: inc x F1 -> False by move: xF1 => /setC_P [].
      have sb: inc y F1 -> False by move: yF1 => /setC_P [].
      case: (splitF _ xF); first by move => [].
      case: (splitF _ yF); first by move => [].
      move => [_ qb qc] [_ qb' qc'].
      case: le2; move => [p1 p2 p3] //.
        move => p4; constructor 3;rewrite p3 in le1.
        case: (QA _ _ le1); last by move=> [_ h0].
        case: (splitF _ zF); move => [ta tb tc].
        move => le4; rewrite - (bcf _ _ _ kn tb qb' le4);split => //.
        by move: ta => /setC_P [].
      constructor 4;split => //; order_tac.
  pose ork k := (graph_on (r1 k) F).
  have dr6: forall k, k <c n -> 
    (total_order (ork k) /\ substrate (ork k) = F).
    move => k kn.
    have srk: substrate (ork k) = F.
      by rewrite /ork graph_on_sr // => a; apply: dr2.
    split; [split |  by exact].
      apply: order_from_rel; split => //.
      by  move => x y z; apply: dr5.
      by  move => x y ; apply: dr4.
      by move => x y xy; move: (dr1 _ _ _ xy) => [xE yE];split; apply: dr2.
      by rewrite srk => x y xE yE; move: (dr3 _ _ _ kn xE yE);
        case => au; [left | right ]; apply /graph_on_P1.
  (** Each order extens the given one *)
  have dr7: forall k x y, k <c n -> gle r x y -> gle (ork k) x y.
    move => k x y kn.
    move: (dr6 _ kn) => [[ori _] sri].
    move /sub_gleP => [xF yF sxy].
    case: (equal_or_not x y) => exy; first by rewrite -exy; order_tac; ue.
    apply /graph_on_P1; split => //.
    case: (splitF _ xF); case: (splitF _ yF);move => [yF1 ry ys] [xF1 rx xs].
    - move: (set1_1 (ra x)); rewrite -xs =>h0; move: (sxy _ h0).
      by rewrite ys => /set1_P => h1; case: exy; rewrite xs ys h1.
    - constructor 2;split => //; left; move => h1.
      move: (set1_1 (ra x)); rewrite -xs =>h0; move: (sxy _ h0).
      by rewrite ys => /setC_P [_] /set1_P.
    - case: (equal_or_not (rb x) (ra y)) => ns; last first.
         case: exy; apply: extensionality =>//.
         rewrite ys xs; move => z /set1_P ->; apply /setC_P. 
         by split => // /set1_P; apply: nesym.
      have Es: E = singleton (rb x).  
        apply: set1_pr => // z zE; ex_middle zb.
        have zx: inc z x by rewrite xs; apply/setC_P;split => //; move /set1_P.
        move: (sxy _ zx); rewrite ys -ns; move /set1_P => //.
      have n1: n = \1c by rewrite - cen Es cardinal_set1.
      constructor 3;split => //.
      move: (bce _ _ kn ry); rewrite srI; move /(NintP nN).
      by rewrite n1; move /clt1; rewrite - succ_zero (cpred_pr2 NS0).
    - case: exy; rewrite xs ys; congr (E -s1 _).
      case: (p_or_not_p (inc (rb y) x)) => h1.
        by move: (sxy _ h1); rewrite {2} ys => /setC_P [_] /set1_P.
      move: h1; rewrite {1}xs => /setC_P aux; ex_middle ok;case:aux;split => //.
      by move /set1_P; apply:nesym.
  (** It remains to show that the intersection is the given ordering 
     We first show that each element of [E] is a greatest element and least *)
  have zz : \0c <c n by apply /strict_pos_P1.
  have zn: inc \0c (Nint n) by  apply /NintP.
  have zd: inc \0c (domain (Lg (Nint n) ork)) by aw.
  case: (emptyset_dichot (Lg (Nint n) ork)) => lne.
       have : inc (J \0c (ork \0c)) (Lg (Nint n) ork).
        by apply /funI_P; ex_tac.
      by rewrite lne; move /in_set0.
  have hii: forall x, inc x E -> exists2 k, k<c n & hi k x = cpred n.
    move => x xE; move: (xE); rewrite -th => xE1.
    move: (bij_surj bh xE1) => [y ys yv].
    move: ys; rewrite sh =>   /(NintP nN)  yn.
    have cpin: inc (cpred n) (Nint n) by apply /NintP.
    set k := Yo (y = cpred n) \0c (csucc y).
    move: (NS_le_nat (proj1 yn) nN) => yN.
    have kn:  k <c n.
      rewrite /k; Ytac cyn => //. 
      rewrite pnv; apply /(cltSleP pnN).
      apply /(cleSltP yN); split => //.
      by apply /(cltSleP pnN); ue. 
    have srhk: (source (hk k)) = (Nint n) by rewrite /hk/shift_mod_n; aw.
    have cpsh: inc (cpred n) (source (hk k)) by rewrite srhk.
    have qh: inc (hi k x) (source (hk k)). 
      by move: (bce _ _ kn xE); rewrite srI srhk.
    move: (bcp _ kn) => [ta tb].
    have tc: inc (cpred n) (source (shift_mod_n n k)).
      by rewrite /shift_mod_n; aw.
    move: (shift_mod_n_ax nN nz (NS_le_nat (proj1 kn) nN)) => td.
    have xv1: x = Vf (hk k) (cpred n).
      rewrite /hk compfV// /shift_mod_n LfV// shift_mod_n_vl //.
      rewrite /k; case: (equal_or_not y (cpred n)) => yp; Ytac0.
        by rewrite (csum0r (CS_nat pnN)); Ytac0; rewrite -yp.
      have ->: cpred n +c csucc y = n +c y.
        by rewrite (csum_nS _ yN) - (csum_Sn _ pnN) -pnv.
      rewrite (Y_false (cleNgt (Nsum_M0le y  nN))).
      by rewrite csumC cdiff_pr1.
    have xt: inc x (target (hk k)) by rewrite xv1; Wtac; fct_tac.
    exists k=> //; apply: (bij_inj tb  qh cpsh).
    by rewrite /hi -/k (inverse_V tb xt).
  have hij: forall x, inc x E -> exists2 k, k<c n & hi k x = \0c.
    move => x xE; move: (xE); rewrite -th => xE1.
    move: (bij_surj bh xE1) => [y ys yv].
    move: ys; rewrite sh => /(NintP nN) yn.
    exists y => //.
    have srhk: (source (hk y)) = (Nint n) by rewrite /hk/shift_mod_n; aw.
    have cpsh: inc \0c (source (hk y)) by rewrite srhk.
    have qh: inc (hi y x) (source (hk y))
      by move: (bce _ _ yn xE); rewrite srI srhk.
    move: (bcp _ yn) => [ta tb].
    have tc: inc \0c (source (shift_mod_n n y)) by rewrite /shift_mod_n; aw.
    move: (shift_mod_n_ax nN nz (NS_le_nat (proj1 yn) nN)) => td.
    have xv1: x = Vf (hk y) \0c.
      rewrite /hk compfV// /shift_mod_n (LfV td zn).
      rewrite shift_mod_n_vl // (csum0l (proj31_1 yn)); Ytac0; ue.
    have xt: inc x (target (hk y)) by rewrite xv1; Wtac; fct_tac.
    apply: (bij_inj tb qh cpsh).
    by rewrite /hi (inverse_V tb xt).
  have dr8: r = intersectionb (Lg (Nint n) ork).
    set_extens t => te.
      have gr: sgraph r by fprops.
      move: (gr _ te); rewrite /pairp; set x := P t; set y := Q t => pt.
      apply: (setIb_i lne); aw => i idn; rewrite LgV//. 
      move: idn => /(NintP nN) => idn.
      move: te; rewrite -pt -/(related r x y) -/(gle r x y).
      rewrite  -/(related (ork i) x y) -/(gle (ork i) x y).
      by apply: dr7.
    move: lne => [xc xcb]; move: (setIb_hi te zd); rewrite LgV// => toz.
    move: (dr6 _ zz); move=> [[orz _] srz].
    have grz: sgraph (ork \0c) by fprops.
    move: (grz _ toz); rewrite /pairp; set x := P t; set y := Q t => pt.
    rewrite -pt -/(related r x y) -/(gle r x y).
    have aux1: forall k, k <c n -> gle (ork k) x y.
      move => k kn.
      have kd: inc k (Nint n)  by apply /(NintP nN).
      have kd1: inc k (domain (Lg (Nint n) ork)) by aw.
      move: (setIb_hi te kd1); rewrite LgV// - pt //.
    have aux: forall k, k <c n -> r1 k x y.
      by move => k kn; move: (aux1 _ kn) => /graph_on_P1 [_ _ ].
    move: (aux1 _ zz) => le1.
    have xF: inc x F by rewrite - srz; order_tac.
    have yF: inc y F by rewrite - srz; order_tac.
    clear xcb toz orz grz le1.
    apply /sub_gleP;split => //.
    case: (splitF _ xF); case: (splitF _ yF); move => [yF1 ry ys] [xF1 rx xs].
          case: (equal_or_not (ra x) (ra y)) => nsv.
            rewrite xs ys nsv; fprops.
          have b1: inc y (F -s F1) -> False by move /setC_P => [].
          have b2: inc x (F -s F1) -> False by move /setC_P => [].
          move: (hii _ rx) => [k kn hl].
          case: (aux _ kn) => [] [p1 p2 p3] //.
          case: (QA _ _ p3) => ww; last by move: ww => [_].
          rewrite ys xs; rewrite (bcf _ _ _ kn rx ry ww); fprops.
        have b2: inc x (F -s F1) -> False by move /setC_P => [].
        have b1: inc y F1 -> False by move: yF1; move /setC_P => [].
        move: (hii _ rx); move => [k kn hl].
        case: (aux _ kn) => [][p1 p2 p3] //.
        case: p3; last by move => [_ ok].
        by move => ta; rewrite xs ys /setC1_P => z /set1_P ->; apply /setC1_P. 
      have b2: inc y (F -s F1) -> False by move /setC_P => [].
      have b1: inc x F1 -> False by move: xF1 => /setC_P  [].
      move: (hij _ ry); move => [k kn hl].
      case: (aux _ kn) => [] [p1 p2 p3] //.
      move=>tb z; rewrite xs => /setC1_P [sa sb].
      move: cen; rewrite pnv -tb hl succ_zero =>  /set_of_card_oneP cen.
      by move: cen sa rx sb=> [q ->] /set1_P -> /set1_P ->.
    have b2: inc y F1 -> False by move: yF1 => /setC_P [].
    have b1: inc x F1 -> False by move: xF1 => /setC_P [].
    move: (hii _ ry); move => [k kn hl].
    case: (aux _ kn) => [] [p1 p2 p3] //.
    case: (QA _ _ p3) => ww; last by move: ww => [_].
    rewrite ys xs; rewrite (bcf _ _ _ kn ry rx ww); fprops.
  exists (Lg (Nint n) ork); split => //.
        hnf;move => k kn; rewrite LgV//; move: kn; aw;trivial => /(NintP nN) kn.
        by move: (dr6 _ kn) ; move => [[ok _] _].
     hnf;aw;move =>k kn; rewrite LgV//;  move: kn =>  /(NintP nN) kn.
     by move: (dr6 _ kn) ; move => [ok _].
   by aw; rewrite card_Nint.
  aw; move => k kn; rewrite LgV//;  move: kn => /(NintP nN) kn.
  by move: (dr6 _ kn) ; move => [_ ->]; rewrite sr.
(** Converse. We first eliminate the case [m=0] *)
move => m mN h.
set F1:= fun_image E singleton.
case: (emptyset_dichot E). 
    by move => ee //; case: nz; rewrite - cen ee // cardinal_set0.
case: (equal_or_not m \0c) => mz.
  move => [a aE]; move: (pd _ aE) (pa _ aE) (pb _ aE) => nab aF bF.
  move: h => [g [A [f [ofg atg cdg asg [_ _ [bf sf tf] _]]]]].
  rewrite sr in sf; rewrite - sf in aF bF.
  case: nab;  apply (bij_inj bf aF bF). 
  have ff: function f by fct_tac.
  move: (Vf_target ff aF) (Vf_target ff bF) => w1 w2.
  move:(order_product_osr ofg)=> [op sp].
  move: (asg); rewrite sp.
  move: tf; rewrite (iorder_sr op asg) => <- pe.
  move: (pe _ w1)(pe _ w2) => /prod_of_substratesP  [qa qb _]
    /prod_of_substratesP  [qc qd _].
  apply: fgraph_exten => //; first by ue.
  rewrite mz in cdg.
  by rewrite qb (card_nonempty cdg) => x /in_set0.
(** Assume [r] is the union of [n] total orders. Let [F] the set of singletons.
    This is finite, nonempty, thus has a greatest element [gei i]
*)
move => [a aE].
move: (Exercise4_10a or mN mz h) =>[g [ofg atg cdg asi ri]].
have fs1: finite_set F1.
  by  apply: finite_fun_image; hnf; rewrite cen;  apply /NatP.
have sdf: sub F1 (substrate r) by  rewrite sr /F/F1 =>t; fprops.
have nef: nonempty F1 by exists (singleton a); apply /funI_P; ex_tac.
pose gei i := the_greatest (induced_order (Vg g i) F1).
have gei_pr: forall i, inc i (domain g) ->
    greatest (induced_order (Vg g i) F1) (gei i).
  move => i idg; move: (atg _ idg) => to1.
  rewrite -(asi _ idg) in sdf.
  move: (finite_subset_torder_greatest to1 fs1 nef sdf) => h1.
  move: (iorder_osr (proj1 to1) sdf)=> [or2 _].
  exact (the_greatest_pr or2 h1).
pose gej i := union (gei i).
have gej_pr: forall i, inc i (domain g) -> 
    (inc (gej i) E /\ singleton (gej i) = gei i).
  move => i idg; move: (gei_pr _ idg) => [h1 _].
  move: (proj1 (atg _ idg)) => o1.
  rewrite - (asi _ idg) in sdf.
  move: h1; rewrite iorder_sr //; move /funI_P => [z ze sz].
  by rewrite /gej sz setU_1.
(** If [m<n], there an element [xc] is not [gei].
 then [singleton xc <= compl_singl xc] for any ordering *)
case: (cleT_el (CS_nat nN) (CS_nat mN)) => // ltmn.
move: (fun_image_smaller (domain g) gej).
set F2:= fun_image (domain g) gej; rewrite cdg => aux.
have ss: ssub F2 E. 
   split.
     by move => t /funI_P [z zdg ->]; case: (gej_pr _ zdg).
   move: (cle_ltT aux ltmn).
   by rewrite  - cen; move => [_ h1]; dneg xx; rewrite xx.
move: (setC_ne ss) => [xc] /setC_P [xce nxcf2].
have cp1: forall i, inc i (domain g) -> 
   gle (Vg g i) (singleton xc) (E -s1 xc).
  move => i idg; move:  (gej_pr _ idg) (gei_pr _ idg) => [qa qb] [].
  have scf1: inc (singleton xc) F1 by  apply /funI_P; exists xc.
  move: (ofg _ idg) => oi.
  rewrite - (asi _ idg) in sdf.
  rewrite (iorder_sr oi sdf) => [_ gt].
  move: (iorder_gle1 (gt _ scf1)) => qc.
  case: (equal_or_not  (gej i) xc) => nexci.
   case: nxcf2; rewrite - nexci; apply  /funI_P; ex_tac.
  have le1: gle r (gei i) (E -s1 xc) by rewrite -qb; apply: pc.
  have le2: gle (Vg g i) (gei i) (E -s1 xc).
    by move: le1; rewrite /gle/related /r ri => le1; apply: setIb_hi.
  order_tac.
case: (emptyset_dichot g) => // ge.
  by case: mz; rewrite - cdg ge domain_set0 cardinal_set0.
have : gle r (singleton xc) (E -s1 xc).
  rewrite /gle/related /r ri; apply: setIb_i => // i idg.
move /sub_gleP => [_ _ hp].
by move: (hp _ (set1_1 xc)) => /setC1_P [_].
Qed.


(** ---- Exercise 4.11 Pure and Mobile sets.

Let's assume that [R] is a set whose elements are finite subsets of [A].
We say that [R] is mobile when, 
if [X] and [Y] are two distinct elements of [R], for any [z] in [X \cap Y]
there is a  subset [Z] of [X \cup Y] in [R] not containing [z].
We say that [P] is pure if no subset of [P] is in [R].  *)

Definition mobile_r R :=  forall X Y, inc X R -> inc Y R -> X <> Y ->
  forall z, inc z (X\cap Y) 
   ->  exists Z, [/\ inc Z R, sub Z (X \cup Y) & ~ (inc z Z)].
Definition min_incl_r R := 
   Zo R (fun z => forall x, inc x R -> sub x z -> z = x).


(** Examples: R is mobile if (a) it contains the empty set, (b) it is formed of  all finite sets whose cardinal is [>n], (c) it is formed of all doubletons, (d)
it contains all singletons (e.g., it is formed of all all sets with 
cardinal [<= n]  *)

Lemma Ex4_11_ex0 R: inc emptyset R -> mobile_r R.
Proof.
move => er x y xr yr xy z zi.
by exists emptyset;split;fprops; move => /in_set0.
Qed.

Lemma Ex4_11_ex1 A n 
   (R := Zo (\Po A) (fun z => finite_set z /\ n <c cardinal z)):
  natp n -> mobile_r R.
Proof.
move => nN X Y /Zo_P []/setP_P XA [fsx nX]/Zo_P [] /setP_P YA [fsy nY] XY z zXY.
have sa: sub ((X \cup Y) -s1 z) (X \cup Y) by move => t /setC1_P [].
move:  (sub_finite_set sa (finite_union2 fsx fsy)) => fsz.
exists ((X \cup Y) -s1 z); split => //; last by move => /setC1_P [].
apply: Zo_i; first by apply /setP_P;move => t /setC1_P []; case /setU2_P;fprops.
split => //.
move: (setI2_2 zXY) => zY.
case: (p_or_not_p (sub X Y)) => sxy.
  move/NatP: fsz; move/setU2id_Pl: (sxy) => -> fsz.
  apply:(clt_leT nX); apply /(cltSleP  fsz); rewrite  - (csucc_pr2 zY).
  by  move/(strict_sub_smaller): fsy; apply.
case: (emptyset_dichot (X -s Y)) => cne. 
    by case: sxy; exact: (empty_setC cne).
move: (rep_i cne); set w := rep (X -s Y) => /setC_P [wa wb].
have ta: sub  ((Y -s1 z) +s1 w) ((X \cup Y) -s1 z).
  move => t /setU1_P; case. 
    move /setC1_P => [pa pb]; apply /setC1_P; fprops.
  move => ->; apply /setC1_P; split;fprops;  contradict wb; ue.
apply: clt_leT (sub_smaller ta).
rewrite csucc_pr; last by  move=> /setC_P [].
by rewrite - (csucc_pr2 zY).
Qed.


Lemma Ex4_11_ex2 A
   (R := Zo (\Po A) (fun z => cardinal z = \2c)):
  mobile_r R.
Proof.
move => X Y /Zo_P [] /setP_P Xa dx /Zo_P [] /setP_P Ya dy xnz z zi.
set Z:= (X \cup Y) -s1 z. 
have ta: sub Z (X \cup Y) by move => a /setC_P [].
exists Z; split => //;last by move => /setC1_P [_].
apply: Zo_i. 
  apply /setP_P; apply: (sub_trans ta); move => a; case /setU2_P; fprops.
move: zi;move /setI2_P => [z1 z2].
have [u unz xu]: exists2 u, u <> z & X = doubleton z u.
  move /set_of_card_twoP: dx => [u [v [unv duv]]].
  move: z1; rewrite duv;case /set2_P; move => ->; first by exists v; fprops.
  by exists u => //;rewrite set2_C.
have [v vnz vu]: exists2 v, v <> z & Y = doubleton z v.
  move /set_of_card_twoP: dy => [w [v [unv duv]]].
  move: z2; rewrite duv; case /set2_P; move => ->; first by exists v; fprops.
  by exists w => //;rewrite set2_C.
have ->: Z = doubleton u v.
  rewrite /Z xu vu; set_extens t.
  move /setC1_P => [sa sb]; case /setU2_P: sa; case /set2_P => // ->; fprops.
  case /set2_P => ->; apply /setC1_P;
    split=> //;  apply /setU2_P; [left | right]; fprops.
by rewrite cardinal_set2 => // uv; case: xnz; rewrite xu vu uv.
Qed.

Lemma Ex4_11_ex3a A R: 
  (forall x, inc x R -> sub x A) ->
  (forall x, inc x A -> inc (singleton x) R) ->  
  mobile_r R.
Proof.
move => RA h X Y xr yr xny z /setI2_P [zX zY].
case: (p_or_not_p (sub X Y)) => xsy.
  move: (rep_i (setC_ne (conj xsy xny))).
  set w := (rep (Y -s X)) => /setC_P [ra rb].
  exists (singleton w);split => //.
      apply: h; apply: (RA _ yr _ ra).
    by move => t /set1_P ->; apply /setU2_P;right.
  move /set1_P; contradict rb; ue. 
have [w wx wny]: exists2 w, inc w X & ~ (inc w Y).
  ex_middle bad; case: xsy => t tx; ex_middle ty; case: bad; ex_tac.
exists (singleton w);split => //.
    apply: h; apply: (RA _ xr _ wx).
  by move => t /set1_P  ->; apply /setU2_P; left.
by move /set1_P => zw; case: wny ; rewrite - zw. 
Qed.
 
Lemma Ex4_11_ex3b A n 
   (R := Zo (\Po A) (fun z => nonempty z /\ cardinal z <=c n)):
    natp n -> n <> \0c -> mobile_r R.
Proof.
move => nb nz.
have pa: (forall x, inc x R -> sub x A).
  by move => x =>/Zo_P [] /setP_P.
apply: (Ex4_11_ex3a pa).
move => x xA; apply: Zo_i; first by apply /setP_P;apply: set1_sub.
split; fprops; rewrite cardinal_set1; apply: cge1;fprops.
Qed.

(** if [R] is mobile, the set of minimal elements of [R] is mobile *)

Lemma Ex4_11_minR_pr R:
   (forall x, inc x R -> finite_set x) ->
   (forall x, inc x R -> exists2 y, sub y x & inc y (min_incl_r R)).
Proof.
move => h x xr.
case: (inc_or_not emptyset R) => eR.
  exists emptyset;fprops;apply: Zo_i => // t tr te.
  apply: extensionality => //; fprops.
set n := cardinal x.
have nN: inc n Nat by apply /NatP; apply: h.
have cxn: cardinal x <=c n by rewrite -/n; fprops.
set B := Zo R (fun z => sub z x).
pose prop k := exists2 x, inc x B & cardinal x <=c k.
have pc: prop n by exists x => //; apply: Zo_i.
case: (least_int_prop2 nN pc).
  move => [y yN cy]; move: (cle0 cy) => cy1.
  move: (card_nonempty cy1) => ye.
  by move: yN => /Zo_P; rewrite  ye; move => [].
set k := cpred; move => [kN [y /Zo_P [yR yx] ck] npk].
exists y=> //; apply: Zo_i => // => z zR zy. symmetry;ex_middle yz.
case: npk; exists z; first by apply: Zo_i=> //; apply: (sub_trans zy yx).
apply / (cltSleP kN); apply: clt_leT ck.
by move/ (strict_sub_smaller):(h _ yR); apply.
Qed.

Lemma Ex4_11_minR_mb R:
   (forall x, inc x R -> finite_set x) ->
   mobile_r R -> mobile_r (min_incl_r R).
Proof.
move => h mb.
move => x y /Zo_P [xR _] /Zo_P [yR _] xy z zi.
move: (mb _ _ xR yR xy _ zi) => [Z [za zb zc]].
move: (Ex4_11_minR_pr h za) => [T ta tb].
exists T; split => //; [ by apply: (sub_trans ta zb) | fprops ].
Qed.

(** We define pure and max pure sets, and compute some of them *)

Definition pure R P:= forall x, sub x P -> ~(inc x R).
Definition set_of_pure A R:= Zo (\Po A) (pure R).
Definition max_pure A R P:= 
 [/\ sub P A, pure R P & forall p, pure R p -> sub P p -> sub p A -> P = p].


Lemma set_of_pureP A R x:
   inc x (set_of_pure A R) <-> (sub x A /\ pure R x).
Proof.  
split; first by  move /Zo_P => [] /setP_P.
by move => [pa pb]; apply: Zo_i => //; apply /setP_P.
Qed.

Lemma Ex4_11_ex0_pure A R : inc emptyset R -> set_of_pure A R = emptyset.
Proof. 
move => er; apply /set0_P => y; apply /set_of_pureP.
move=>[_ h]; apply: h er; fprops.
Qed.

Lemma Ex4_11_ex1_pure A n
  (R := Zo (\Po A) (fun z => finite_set z /\ n <c cardinal z)):
  inc n Nat -> 
  [/\  set_of_pure A R = Zo (\Po A) (fun z => cardinal z <=c n),
    (n <=c cardinal A -> 
     forall M, sub M A -> (max_pure A R M <-> cardinal M = n)) &
    (cardinal A  <=c n ->
      (set_of_pure A R = \Po A
      /\ (forall M, max_pure A R M <-> M = A)))].
Proof.
move => nN.
have pa: forall P, sub P A -> pure R P -> cardinal P <=c n.
  move => p pa pb.
  case: (cleT_el (CS_cardinal p) (CS_nat nN)) => // h.
  case: (finite_or_infinite (CS_cardinal p)) => fcp.
    by case: (pb _ (@sub_refl p)); apply: Zo_i => //;apply /setP_P.
  have fsc: finite_c (csucc n) by apply /NatP; fprops.
  move: (card_card (CS_succ n)) => csn.
  move: (cle_fin_inf fsc fcp).
  rewrite - csn; move => /eq_subset_cardP1/set_leP [z zp]. 
  move /card_eqP; rewrite  csn => zc.
  case: (pb _ zp);apply: Zo_i.
      apply /setP_P; apply: (sub_trans zp pa).
  split; first by rewrite /finite_set - zc; apply /NatP; fprops.
  rewrite - zc; fprops.
have pb: forall P, (sub P A /\ cardinal P <=c n) -> pure R P.
  move => p [qa qb].
  move => x xp xr; move: (sub_smaller xp) => le1.
  move: (cleT le1 qb) => le2.
  by move: xr => /Zo_P [_ [_ /(cleNgt le2)]].
split.
    set_extens t; move /Zo_P => [ta tb]; apply /Zo_P;split => //.
       by apply: pa => //; apply /setP_P.
    by apply: pb;split => //;apply /setP_P.
   move => ca M mc; split.
     move => [_ ma mb]; ex_middle ce1; move: (pa _ mc ma) => le1.
     have cm: cardinal M <c n by split.
     have ss: ssub M A.  
       by split => // bad; rewrite -bad in ca; case: ce1; apply:cleA.
     move: (rep_i (setC_ne ss)); set w := rep _.
     move => /setC_P [sa sb];  move: (csucc_pr sb);  set p := M +s1 w => cp.
     have sp: sub p A.
        by  move => t; case/setU1_P; [apply: mc | by move => -> ].
     have pp: pure R p.
       apply: pb; split => //; rewrite cp; apply /cleSlt0P; fprops.
     have mp: sub M p by move => t tm ; apply /setU1_P; fprops.
     case: sb; rewrite (mb _ pp mp) //; rewrite /p; fprops.
  move => cm; split => //; first  by apply: pb; split => //; rewrite cm; fprops.
  move => p pp mp spa; move: (pa _ spa pp) => px.
  have fsm: finite_set p  by  apply /NatP; apply:(NS_le_nat px nN).
  by apply: (strict_sub_smaller_contra fsm mp); apply: cleA; [apply:sub_smaller | ue].
move => le1.
have pd: (forall M, sub M A -> pure R M).
  move => m ma; apply: pb; split => //; exact: (cleT (sub_smaller ma) le1).
split.
  set_extens t; first by move /Zo_P => [].
  by move /setP_P => ta; apply /set_of_pureP;split => //; apply: pd.
have pra: pure R A by apply: pd.
move => M; split; first by move => [ma sa mb]; apply: mb => //.
move => ->; split => //; move => p _; apply: extensionality.
Qed.

Lemma Ex4_11_ex2_pure A
  (R := Zo (\Po A) (fun z => cardinal z = \2c)):
  (set_of_pure A R = Zo (\Po A) small_set
    /\ ( nonempty A ->
         forall M, max_pure A R M <-> (sub M A /\ singletonp M))).
Proof.
have pa:forall M, sub M A -> small_set M -> pure R M.
  move => M ma mb x xm => /Zo_P.
  move =>[_ cx2]; move: (sub_smaller xm); rewrite cx2.
  move /(cle2P); move => [a [b [am bm ab]]].
  by case: ab;apply: (mb _ _ am bm).
have pb: forall M, sub M A -> pure R M -> small_set M.
  move => M ma mb a b am bm; ex_middle ab.
  have sd: sub (doubleton a b) M by move => t; case /set2_P => ->.  
  case: (mb _ sd); apply: Zo_i => //;  last by apply: cardinal_set2.
  by apply /setP_P;apply:(sub_trans sd ma).
split.
   set_extens t => /Zo_P [ta tb];apply: Zo_i => //;
      [ apply: pb | apply: pa] => //; apply /setP_P => //.
move => neA M; split. 
  move => [mc ma mb];move: (pb _ mc ma) => md; split; first by exact.
  case: (small_set_pr md) => // me.
  move: (rep_i neA) => rA.
  have qa: sub (singleton (rep A)) A by apply: set1_sub.
  have ps: pure R (singleton (rep A)).
    by apply: pa;  [ move => t /set1_P => -> | apply: small1].
  have sms: sub M (singleton (rep A)) by rewrite me; fprops.
  by rewrite (mb _ ps sms qa); exists (rep A).
move => [ma [t st]]; split => //.
  by apply:pa => //; move => a b; rewrite st; move => /set1_P -> /set1_P ->.
move: (set1_1 t); rewrite - st => tm.
move => p pp mp pra; move: (pb _  pra pp) =>  py; apply: extensionality => //.
by move => s sp; rewrite (py _ _ sp (mp _ tm)).
Qed.

Lemma Ex4_11_ex3_pure A R:
  (forall x, inc x A -> inc (singleton x) R) ->
  (forall M, sub M A -> pure R M -> M = emptyset).
Proof.
move => asr m ma mb; case: (emptyset_dichot m) => em //.
move: (rep_i em) => rm.
by move: (set1_sub rm) => sm; case: (mb _ sm); apply: asr; apply: ma.
Qed.

Lemma Ex4_11_minR_P2 R: 
   (forall x, inc x R -> finite_set x) ->
   (forall P, pure R P <-> pure (min_incl_r R) P).
Proof.
move => fr p; split.
  by move => pr x xp bad; apply: (pr _ xp); move: bad => /Zo_P [].
move =>  pr x xp xR; move: (Ex4_11_minR_pr fr xR) => [y yx ym].
case: (pr _ (sub_trans yx xp) ym).
Qed.

(** We define [mobile_ext] to have all properties but minimality. 
Adding minimality does not change the set of pures. We give a characteristic 
property of the pures  *)

Definition mobile_ext R A:=
  [/\ (forall x, inc x R -> sub x A),
      (forall x, inc x R -> finite_set x),
       mobile_r R  &
      ~ (inc emptyset R)].
  

Lemma Ex4_11_minR_pr3 A R (R' := min_incl_r R):
  mobile_ext R A ->
  (mobile_ext R' A /\ set_of_pure A R =  set_of_pure A R').
Proof.
move => [pa pb pc pd]; move: (Ex4_11_minR_mb pb pc) => pe.
split;last first.
    by set_extens t => /set_of_pureP [ta tb]; apply /set_of_pureP;split => //;
      move: tb; move /(Ex4_11_minR_P2 pb).
have ta: ~ inc emptyset R' by  move /Zo_P => [ta] _.
split => // w => /Zo_S wr;fprops.
Qed.

Definition pure_prop1 A S := 
  (nonempty S) /\ (forall x, inc x S -> sub x A).
Definition pure_prop2 S := 
  (inductive (sub_order S)).
Definition pure_prop3 A S := 
  (forall M N, sub M A -> sub N A -> ~ inc M S ->  ~ inc N S ->
    inc (M \cap N) S ->
    forall x, inc x (M \cup N) -> ~ (inc ((M \cup N) -s1 x) S)).
Definition pure_prop4  S :=
  (forall x y, inc x S -> sub y x -> inc y S).
Definition pure_prop5 A S :=
  forall x, sub x A -> ~ (inc x S) -> 
     exists y, [/\ sub y x, finite_set y & ~ (inc y S)].

Lemma pure_properties_res1 A R:
  mobile_ext R A -> (pure_prop2 (set_of_pure A R)).
Proof.
move => [pa pb pc pd].
set or := (sub_order (set_of_pure A R)).
move => X xsp tor.
move: (sub_osr (set_of_pure A R)) => [ora sra].
move: (xsp); rewrite sra => xsp1.
exists (union X); hnf; rewrite  sra.
suff: inc (union X) (set_of_pure A R).
   move => up; split => // y yX; apply/sub_gleP;split;fprops.
   by apply: setU_s1.
have sa: sub (union X) A.
  by apply: setU_s2 => y yX; move: (xsp1 _ yX) => /Zo_P [] /setP_P.
apply: Zo_i; [ by apply /setP_P | move => x xsu xR; move: (pb _ xR) => fy].
pose f t:= choose (fun i =>  inc t i /\ inc i X).
have fp: forall t, inc t x -> (inc t (f t) /\ (inc (f t) X)).
  move => t tx; apply choose_pr; move: (xsu _ tx) => /setU_P.
  by move => [s s1 s2]; exists s.
move: (finite_fun_image f fy) ; set imf:= fun_image x f => fi.
case: (emptyset_dichot x) => xne; first by case: pd; ue.
have ine: nonempty imf.
  rewrite /imf;move: xne => [t tx]; exists (f t); apply /funI_P;ex_tac.
set r' := induced_order or X.
move: (iorder_osr ora xsp)=> [or' sr''].
have ssr: sub imf (substrate r').
   rewrite sr'' // => t /funI_P [z zx ->].
   by move: (fp _ zx) => [_].
move: (finite_subset_torder_greatest tor fi ine ssr) => [u []].
rewrite iorder_sr // => ui ug.
move: (ui) => /funI_P [v vx fv].
move: (fp _ vx); rewrite -  fv; move => [_ uX].
move: (xsp1 _ uX) => /Zo_hi  pu.
have pe: sub x u.
   move=> t tx; have pe: inc (f t) imf by apply /funI_P; ex_tac.
   move: (iorder_gle1 (iorder_gle1 (ug _ pe))) => /sub_gleP.
   by move => [_ _ h]; move: (fp _ tx) => [h2 _]; apply: h.
by move: (pu _ pe).
Qed.


Lemma pure_properties_res2 A R (S:= set_of_pure A R):
  mobile_ext R A -> 
  [/\ pure_prop1 A S, pure_prop2 S, pure_prop3 A S,
  pure_prop4 S &  pure_prop5 A S]. 
Proof.
move => h;  move: (pure_properties_res1 h) => pe.
move: h => [pa pb pc pd].
have auxP: forall s, sub s A ->
  ( ~ (inc s (set_of_pure A R)) <-> (exists2 y, sub y s & inc y R)).
  move => s sA; split.
    move  /set_of_pureP =>h; ex_middle bad.
     case: (p_or_not_p (pure R s)) => ps; first by case: h; split => //.
     by case: ps => x xs xr ; case: bad; exists  x.
  by move => [u ys yr] /set_of_pureP [sa pr];move: (pr _ ys yr).
have p5: pure_prop5 A S.
  move => x xA; move /(auxP _ xA) => [y yx yr].
  by exists y; split;fprops;apply /(auxP _ (sub_trans yx xA)); exists y. 
have p4: forall x y, inc x S -> sub y x -> inc y S.
    move => x y /set_of_pureP [xA pr] yx; apply /set_of_pureP.
split; first by apply: (sub_trans yx xA).
    move => v vy vr; exact: (pr _ (sub_trans vy yx) vr).
split => //.
  split.
    exists emptyset; apply/set_of_pureP; split;fprops.
    by move => x; move/ sub_set0 => ->.
  by move => x /set_of_pureP [].
move => M N MA NA nM nN iR x xu.
have sa: sub ((M \cup N) -s1 x) A.
  by move  => t /setC1_P [ta _]; case /setU2_P:ta; [apply: MA | apply: NA].
apply / (auxP _ sa).
move: nM nN => /(auxP _ MA) [M' mm' mr] /(auxP _ NA)  [N' nn' nr].
case: (equal_or_not M' N') => nmn.
  have qd: sub M' (M \cap N). 
     move => t tm'; apply /setI2_P; split;[fprops | apply: nn'; ue].
  by move: iR => /set_of_pureP [_ h]; move: (h  _ qd). 
case: (inc_or_not x (M' \cap N')) => xi.
  move: (pc _ _ mr nr nmn _ xi) => [Z [zr za zb]]; ex_tac.
  move => t tz. 
  have tx: t <> x by dneg tx; ue.
  move: (za _ tz); case /setU2_P => tt; 
       apply /setC1_P;split => //; apply /setU2_P;[left | right]; fprops.
case: (inc_or_not x M') => xm'.
have xn': ~ (inc x N') by  move => bad; case: xi; apply /setI2_P.
   exists N' => // t tn'; apply /setC1_P;split;[fprops |  dneg tx; ue].
exists M' => // t tn'; apply /setC1_P;split;[fprops |  dneg tx; ue].
Qed.


Lemma pure_properties_res3: exists A S,
  [/\ pure_prop1 A S, pure_prop2 S, pure_prop3 A S, pure_prop5 A S &
   ~  (pure_prop4 S)]. 
Proof.
have xx: (substrate (sub_order (singleton C2))) = (singleton C2).
  by rewrite (proj2 (sub_osr _)).
exists C2; exists (singleton C2); split => //.
by split; fprops; move => x /set1_P ->; fprops.
  move => h ha _; exists C2; hnf; rewrite xx;split;fprops.
  move => y yh;  move: (ha _ yh); rewrite xx;aw; move /set1_P=> ->.
  by apply /sub_gleP;split;fprops.
move => m n ma mn /set1_P ta /set1_P tb /set1_P tc.
  case: ta; apply: extensionality => //; rewrite -tc. 
  by apply: subsetI2l.
move => x xtp /set1_P xntp; exists emptyset; aw; split;fprops.
    apply: emptyset_finite.
  by move /set1_P => tpe; symmetry in tpe; empty_tac1 C0.
move => h;  move: (set1_1 C2) => ta.
  have tb: sub (singleton C0) C2 by  move => t /set1_P ->; fprops.
  by move: inc_C1_C2; move: (h _ _ ta tb) => /set1_P <- /set1_P; fprops.
Qed.

Lemma pure_properties_res4 A S:
  (pure_prop2 S) -> (pure_prop4 S) ->  (pure_prop5 A S).
Proof.
move => p2 p4.
move => M MA nMS.
case: (finite_or_infinite_set M) => ifm; first by exists M; split. 
set T := fun_image (Zo (\Po M) (fun z => ~(inc z) S)) cardinal.
have zt: inc (cardinal M) T.
apply /funI_P; exists M => //; apply: Zo_i; aww; apply :setP_Ti.
have cst: cardinal_set T by move => t /funI_P  [y _ ->]; fprops.
move: (wordering_cle_pr cst) => [[tb tc] ta].
rewrite ta in tc.
have net: nonempty T by ex_tac.
move: (tc _ (@sub_refl T) net) => [cy []].
rewrite iorder_sr //; last by rewrite ta; fprops.
move => cyt aux1.
have cym: forall y, inc y T -> cy <=c y. 
  move => y yt.
  by move: (iorder_gle1 (aux1 _ yt)) => /graph_on_P1 [_ _].
move: cyt => /funI_P [N pa cN]. 
move: pa => /Zo_P [] /setP_P NL nNS.
have icy: cardinalp cy by rewrite cN; fprops.
case: (finite_or_infinite icy) => ifcy.
  by exists N;split => //; rewrite /finite_set - cN.
move: (infinite_card_limit2 ifcy) => [ya ocy ly].
move: cN; rewrite -(card_card icy);move /card_eqP=> [f [bf sf tf]].
pose vfi i := Vfs f i.
have ff: function f by fct_tac.
have fa: forall i, i <=o cy -> sub i (source f). 
  by move => i ic; rewrite sf; move: ic => [_ _ ].
have fb: forall i j, i<=o cy -> j <=o cy -> i <=o j -> sub (vfi i) (vfi j).
  move => i j iy jy ji t; rewrite /vfi; move: (fa _ iy) (fa _ jy) => isf jsf. 
  move => /(Vf_image_P ff isf) [u ui wu]; apply /(Vf_image_P ff jsf). 
  by exists u => //; move: ji => [_ _ ]; apply.
have sc: forall i, i <o cy -> cardinal (vfi i) <c cy.
   move => i iy; rewrite /vfi.
   have -> : cardinal (Vfs f i)  = cardinal i.
     symmetry; apply /card_eqP.
     move: (fa _ (proj1 iy)) => sfa.
     move: (restriction1_fb (proj1 bf) sfa) => bf1.
     by exists (restriction1 f i); split => //; rewrite /restriction1; aw.
  by apply /(ocle2P icy (proj31_1 iy)). 
have sd: forall i, i <o cy -> inc (vfi i) S.
  move => i iy; move: (sc _ iy) => cs; ex_middle nvs.
  have cvt: inc (cardinal (vfi i)) T.
     apply /funI_P;exists  (vfi i) => //;apply: Zo_i => //.
     by apply/setP_P;apply: sub_trans NL; rewrite -tf; apply:fun_image_Starget1.
  case: (cltNge cs (cym _ cvt)).
set Z:= fun_image cy vfi.
have za: sub Z S.  
   move => t /funI_P [z zy ->]; apply: sd.
   by move: zy => /(oltP ya).
move:(sub_osr S) => [zc pb].
have zb: sub Z (substrate (sub_order S)) by ue.
move: (iorder_osr zc zb) => [wa wb].
have zd: total_order (induced_order (sub_order S) Z).
  split; fprops. rewrite wb; move => x y xz yz; rewrite /ocomparable.
  move: (xz)(yz) => /funI_P [x' xy vx] /funI_P [y' yy vy].
  have [le1 _]: x' <o cy by move:  xy => /(oltP ya).
  have [le2 _]: y' <o cy by move:  yy => /(oltP ya).
  by case: (oleT_ee (proj31 le1) (proj31 le2)) => h; [left | right ];
    apply /iorder_gle0P => //; apply /sub_gleP;split;fprops;
    rewrite vx vy; apply: fb.
move: (p2 Z zb zd) => [X []]; rewrite pb => X1 X2.
have aux: forall i, i <o cy -> sub (vfi i) X.
  move => i iy. 
  have h: inc  (vfi i) Z. 
    by apply /funI_P;exists i => //; move:  iy => /(oltP ya).
  by move: ( X2 _ h) => /sub_gleP [_ _].
have nt: sub N X.
  move => t; rewrite -tf => ttf; move: (bij_surj bf ttf) => [x xsf ->].
  move: xsf; rewrite sf => xcy.
  move: (ly _ xcy) => scy.
  have td: (osucc x) <o cy by apply /oltP.
  have ax2: sub (osucc x) (source f). apply: fa (proj1 td).
  move: (aux _ td); apply; apply /(Vf_image_P ff ax2); exists x => //.
  rewrite /csucc; fprops.
by move: (p4 _ _ X1 nt).
Qed.

Lemma pure_properties_res5 A S:
 pure_prop1 A S -> pure_prop3 A S -> pure_prop4 S -> pure_prop5 A S ->
 exists R, 
    [/\ mobile_ext R A,
        S = (set_of_pure A R) &
        (forall x z, inc x R -> inc z R -> sub x z -> z = x)].
Proof.
move => [nes p1] p3 p4 p5.
set R := Zo (\Po A)(fun z => ~(inc z S) /\
    forall v, sub v z -> ~ (inc v S) -> v = z).
have pa: (forall x z, inc x R -> inc z R-> sub x z -> z = x).
  move => x z /Zo_P [_ [xs _]] /Zo_hi [_ zp] h.
  by symmetry; apply: zp.
have pb: forall x, inc x R -> sub x A.
  by move => x /Zo_P [] /setP_P.
have pc: ~ inc emptyset R.
  move  /Zo_P =>[ta [tc _]]; case: tc.
  move: nes => [w ws]; apply:(p4 w emptyset) => //; fprops.
have pd: (forall z, inc z R -> finite_set z).
  move => z => /Zo_P [] /setP_P ta [tb tc].
  move: (p5 _ ta tb) => [y [ys fsy nys]].
  by rewrite - (tc _ ys nys).
have pe: forall M, sub M A -> ~ (inc M S) -> exists2 N, sub N M & inc N R.
  move => M MA nMS.
  move: (p5 _ MA nMS) => [y [ym fy nys]].
  set T := Zo (\Po y) (fun z => ~ (inc z S)).
  have tf: (forall x, inc x T -> finite_set x).
     move => x /Zo_P [] /setP_P xy _.
     apply: (sub_finite_set xy fy).
  have yt: inc y T by apply: Zo_i => //; apply /setP_P.
  move: (Ex4_11_minR_pr tf yt) => [z zt] /Zo_P [ta tb].
  move: (sub_trans zt ym) => zM.
  exists z=> //; apply: Zo_i; first by apply /setP_P; apply: (sub_trans zM MA).
  move: ta => /Zo_P [_ zs]; split => //.
  move => v vz nvs; symmetry; apply: tb => //; apply: Zo_i => //. 
  apply /setP_P; apply: (sub_trans vz zt).
have pf: mobile_r R.
  move => M N MR NR; move: (MR) (NR) => /Zo_P []  /setP_P MA [nMS Mm]
     /Zo_P  [] /setP_P NA [nNS Nm] MN z zi.
  have qa: inc (M \cap N) S. 
     move: (@subsetI2l M N)(@subsetI2r M N) => ta tb.
     ex_middle ins; move: (Mm _ ta ins) => tc; case: MN; apply: Nm => //; ue. 
  have qb: inc z (M \cup N) by move: zi=> /setI2_P [zm _]; apply /setU2_P; left.
  move: (p3 _ _ MA NA nMS nNS qa _ qb).
  set Z := ((M \cup N) -s1 z) => zs.
  have zc: sub Z (M \cup N) by move => t /setC1_P [].
  have za: sub Z A by apply: (sub_trans zc) => t; case /setU2_P =>h; fprops.
  move: (pe _ za zs) => [Z' Z1 Z2]; exists Z'; split => //.
     apply: (sub_trans Z1 zc).
  by move => h; move: (Z1 _ h) => /setC1_P[].
have pg: S = set_of_pure A R.
  set_extens t.
     move => tS; apply /set_of_pureP;split;fprops.
      move => x xp => /Zo_P [_ [bad xb]]; case: bad; exact: (p4 _ _ tS xp).
  move  /set_of_pureP =>  [ta pt]; ex_middle ts.
  move: (pe _ ta ts) => [N nt nr]; by move: (pt _ nt).
by exists R. 
Qed.

Lemma pure_properties_res6 A S:
 pure_prop1 A S -> pure_prop2 S -> pure_prop3 A S -> pure_prop4 S ->
 exists R, 
    [/\ mobile_ext R A,
        S = (set_of_pure A R) &
      (forall x z, inc x R -> inc z R -> sub x z -> z = x)].
Proof.
move => p1 p2 p3 p4; apply: pure_properties_res5 => //.
by apply: pure_properties_res4.
Qed.

Definition mobile_alt R :=
  forall E F, inc E R -> inc F R -> E <> F ->
  forall x y, inc x (E \cap F) -> inc y (E -s F) ->
  exists G, [/\ inc G R, sub G (E \cup F), inc y G & ~ (inc x G)].

Lemma pure_properties_res7 A R:
  (forall x, inc x R -> sub x A) -> 
  (forall x, inc x R -> finite_set x)  -> ~ (inc emptyset R) ->
  (forall x z, inc x R -> inc z R -> sub x z -> z = x) ->
  (mobile_r R <-> mobile_alt R).
Proof.
move => ra rf ner rmin; split; last first.
  move => h X Y Xr Yr XnY z zi.
  case: (emptyset_dichot (Y -s X)) => ce.
    move: (empty_setC ce) => yx.
    case: (emptyset_dichot (X -s Y)) => ce1.
      by move: (empty_setC ce1) => xy; case: XnY; apply:extensionality.
    move: ce1 => [y yc].
    move: (h _ _ Xr Yr XnY _ _ zi yc) => [w [z1 z2 z3 z4]].
    by exists w.
  have XnY': Y <> X by apply:nesym.
  move: ce => [y yc].
  rewrite setU2_C; rewrite setI2_C in zi.
  move: (h _ _ Yr Xr XnY' _ _ zi yc) => [w [z1 z2 z3 z4]].
   by exists w.
move => mr.
pose am E F :=   forall x y, inc x (E \cap F) -> inc y (E -s F) ->
  exists G, [/\ inc G R, sub G (E \cup F), inc y G & ~ (inc x G)].
set T := Zo (coarse R) (fun z =>  (P z <> Q z /\ ~(am (P z) (Q z)))).
case: (emptyset_dichot T) => nte.
  move => E F p1 p2 p3; ex_middle bad.
  empty_tac1 (J E F); apply: Zo_i; [ by apply :setXp_i | saw].
pose prop x := exists2 z, inc z T & cardinal (P z \cup Q z) <=c x.
move: nte => [z zT]; move: (zT) => /Zo_P [] /setX_P [_ pr qr] _.
have pc: prop (cardinal (P z \cup Q z)) by exists z;fprops.
have pcN: natp (cardinal (P z \cup Q z)).
  by apply /NatP; apply: finite_union2;apply: rf.
case: (least_int_prop2 pcN pc).
   move => [z' zt cu]. 
   move: (card_nonempty (cle0 cu)) => ue.
   move: zt => /Zo_P [] /setX_P [_ pr' _] _.
   have pe: P z' = emptyset by apply /set0_P => t tp; empty_tac1 t; aw; left.
   case: ner; by ue.
set m := cpred _ ; move=> [mN [zm zmt czm] smp].
have smp' t: inc t T -> csucc m <=c  cardinal (P t \cup Q t).
  move => zt.
  have cc1: cardinalp (csucc m) by fprops.
  have cc2: cardinalp (cardinal (P t \cup Q t)) by fprops.
  case: (cleT_el cc1 cc2) => //; move /(cltSleP  mN) => cc3.
  case: smp; hnf; ex_tac.
have czm'':= (cleA czm (smp' _ zmt)).
move: zmt => /Zo_P [] /setX_P; set E := P zm; set F := Q zm.
move => [_ ER FR] [EnF namEF]; rewrite -/E -/F in czm''.
have smp'': forall U V, inc U R -> inc V R -> U <> V -> 
    cardinal (U \cup V) <c csucc m -> am U V.
  move => U V ur vr uv cle; ex_middle bad.
  have aux: inc (J U V) T by apply: Zo_i; aw; fprops; apply /setXp_P.
  by move: (smp' _ aux); aw => /(cltNge cle).
case: namEF; move => x y xEF yEF.
move: (xEF) => /setI2_P [xE xF].
move: (mr _ _ ER FR EnF _ xEF) => [G [GR Gu xG]].
case: (inc_or_not y G) => yG; first by exists G.
case: (emptyset_dichot (G -s E)) => nge.
   case: yG; rewrite - (rmin _ _ GR ER (empty_setC nge)). 
   by move: yEF; case /setC_P.
move: (rep_i nge); set t := rep _ => zd.
have fsa: finite_set (E \cup F) by apply /NatP ; ue.
have cs1: cardinal  (F \cup G) <c csucc m.
  rewrite setU2_C - czm''; move/ strict_sub_smaller: fsa; apply.
  move: yEF => /setC_P [ya yb].
  split => bad; first by  case /setU2_P; fprops. 
  have: inc y (E \cup F) by  fprops.
  by rewrite - bad; case /setU2_P.
have nGF: F <> G by move => bad; case: xG; ue. 
have xGF: inc x (F -s G) by apply /setC_P.
have zGF: inc t (F \cap G). 
  move: zd => /setC_P[za zb]; apply /setI2_P; split => //; move:(Gu _ za). 
  case/setU2_P => //.
move: (smp'' _ _ FR GR nGF cs1 _ _ zGF xGF).
move => [H [HR hfg xH zH]].
have ss0: sub (E \cup H) (E \cup F).
  move => t'; case /setU2_P; [ fprops | move => xh].
  move: (hfg _ xh) => /setU2_P; case; [fprops | apply: Gu].
have cs2: cardinal  (E \cup H) <c csucc m.
  rewrite - czm''; move/strict_sub_smaller: fsa; apply.
  split; [exact |  move => bad].
  have: inc t (E \cup F) by  move: zGF => /setI2_P [sa _]; fprops.
  by rewrite - bad; case /setU2_P => //; move: zd => /setC_P [].
have yEH: inc y (E -s H). 
  move: yEF => /setC_P [ye nyf]; apply /setC_P;split => //.
  move => yh; case: nyf; move: (hfg _ yh); case /setU2_P=> //.
have nEH: E <> H by move => bad; move: yEH => /setC_P; rewrite bad; case.
have xEH: inc x (E \cap H) by fprops.
move: (smp'' _ _ ER HR nEH cs2 _ _ xEH yEH).
move => [K [KR kfg xK yK]];exists K;split => //; apply: (sub_trans kfg ss0).
Qed.

Definition ppr8_hyp R f n:=
  [/\ fgraph f, domain f = Nint n,
  (forall i, i <c n -> inc (Vg f i) R) &
  (forall i, i<c n ->
       ~ (sub (Vg f i) (unionb (restr f (Nint i)))))].

Definition ppr8_conc R B f g  m:=
  [/\ fgraph g, domain g = Nint m,
  (forall i, i <c m -> inc (Vg g i) R),
  (forall i, i <c m -> sub (Vg g i) (unionb f -s B)) &
  (forall i, i<c m ->
       ~ (sub (Vg g i) (unionb (restr g ((Nint m) -s1 i)))))].


Lemma pure_properties_res8 A R:
   mobile_ext R A ->
   (forall x z, inc x R -> inc z R -> sub x z -> z = x) ->
   forall r m, inc r Nat -> natp m -> m <> \0c ->
     forall f B, ppr8_hyp R f (m +c r) -> cardinal B = r ->
     exists g, ppr8_conc R B f g  m.
Proof.
move=>  [srA fsa mr ner] minr.
move: (mr); rewrite (pure_properties_res7 srA fsa ner minr) => mr'.
pose p E F x y G:=  [/\ inc G R, sub G (E \cup F), inc y G& ~ (inc x G)].
pose cmr E F x y := choose (p E F x y).
have cmrp: forall E F x y, inc E R -> inc F R -> inc x (E \cap F) 
   -> inc y ( E -s F) -> p E F x y (cmr E F x y).
  move => E F x y er fr xef yef; apply:choose_pr. 
  have ef: E <> F by move => ef; move: yef=> /setC_P []; rewrite ef.
  exact (mr' _ _ er fr ef x y xef yef) . 
have ind0:  forall m, natp m -> m <> \0c ->
     forall f, ppr8_hyp R f m -> exists g, ppr8_conc R emptyset f g  m.
  move => m mN mnz f [fgf df fR unp].
  pose xv i := rep ((Vg f i) -s (unionb (restr f (Nint i)))).
  have xvp1: forall i, i <c m -> 
     inc (xv i) ((Vg f i) -s (unionb (restr f (Nint i)))).
     move => i im; move: (unp _ im); rewrite /xv; set s := unionb _ => ss.
     apply: rep_i; case: (emptyset_dichot (Vg f i -s s)) => // ve.
     by move: (empty_setC ve).
  have xvp2: forall i, i<c m -> inc (xv i) (Vg f i).
    by move => i im; move: (xvp1 _ im)=> /setC_P [].
  have dd: forall i, i<c m -> sub (Nint i) (domain f).
     move => i im;move: (proj1 im) => im1.
     have iN: inc i Nat by apply: (NS_le_nat im1 mN).
     rewrite df; apply:Nint_M1 => //. 
  have xvp3: forall i j, j <c i -> i <c m -> ~(inc (xv i) (Vg f j)).
     move => i j ji im xvi; move: (xvp1 _ im)  => /setC_P [_]; case.
     have iN: natp i by apply: (NS_le_nat (proj1 im) mN).
     have aux: inc j (Nint i) by  apply /(NintP iN).
     move : (dd _ im) => dmf; apply /setUb_P;aw; exists j => //; rewrite LgV//.
  clear xvp1.
  pose nextB i Bi:= 
       Lg Nat (fun j => Yo (inc (xv i) (Vg Bi j)) 
          (cmr (Vg Bi j) (Vg Bi i) (xv i) (xv j)) (Vg Bi j)).
  move: (induction_term0 nextB f) (induction_terms nextB f).
  set fB := induction_term nextB f => fBa fBb.
  pose B i j := Vg (fB i) j.
  have Ba: forall j, B \0c j = Vg f j.
    by move  => j; rewrite /B fBa. 
  have Bp: forall i, natp i -> forall j, i<=c j -> j <c m ->
    [/\ inc (B i j) R,
     sub (B i j) (Vg f j \cup (unionb (restr f (Nint i)))),
     inc (xv j) (B i j),
     (forall k, k <c i -> ~ (inc (xv k) (B i j))) &
     (forall k, j <c k -> k <c m -> ~ (inc (xv k) (B i j)))].
    apply: Nat_induction.
      move => j jz jm; rewrite Ba; split;fprops.
          apply: subsetU2l.
      by move => k k0; case: (clt0 k0).
    move => i iN Hrec j cji cjm.
    have jb: natp j  by apply (NS_le_nat (proj1 cjm) mN).
    rewrite /B; rewrite (fBb _ iN) /nextB (LgV  jb).
    move: (cleT (cleS iN) cji) => cij.
    move: (dd _ (cle_ltT cji cjm)) => dr2.
    move: (dd _ (cle_ltT (cleS iN) (cle_ltT cji cjm))) => dr1.
    have -> : (Vg (fB i) j) = B i j by rewrite /B.
    move: (Hrec _ cij cjm)=> [pe pa pb pc pd].
    have tg: sub (unionb (restr f (Nint i)))
         (unionb (restr f (Nint (csucc i)))).
       move => y /setUb_P; aw ; move=> [z zi]; rewrite LgV//.
      have zi':inc z (Nint (csucc i)).
        by move: (Nint_M iN zi) => zi' => //; rewrite LgV.
       move => yv; apply  /setUb_P; aw; ex_tac; rewrite LgV//.
    Ytac aux; last first.
      split => //.
        move => t tb; move: (pa _ tb) => /setU2_P tu; apply /setU2_P.
        case: tu => tu; [by left | by right; apply: tg].
      move => k ksi.
        case: (equal_or_not k i) => ki; first by rewrite ki.
        by apply: pc;split => //; apply /(cltSleP iN).
    move: (Hrec _ (cleR (proj31 cij)) (cle_ltT cij cjm))
      => [qe qa qb qc qd].
    have lij: i<c j by apply /cleSltP.
    have ta: inc (xv i) (B i j \cap Vg (fB i) i) by fprops.
    have tb: inc (xv j) (B i j -s Vg (fB i) i)
          by  apply /setC_P;split => //; apply: qd.
    move: (cmrp _ _ _ _ pe qe ta tb); set c := cmr _ _ _ _.
    move => [tc td te tf].
    have th: sub c (Vg f j \cup unionb (restr f (Nint (csucc i)))).
      move => t itc; move: (td _ itc); case /setU2_P=> tic'; apply /setU2_P.
        move: (pa _ tic'); case  /setU2_P=> tic''; first by left.
        by right; apply: tg.
      move: (qa _ tic'); case /setU2_P=> tv; right; last by apply:tg.
      have ii: inc i (Nint (csucc i)) by apply :Nint_si.
       apply /setUb_P; aw; ex_tac; rewrite LgV//; split => //.
   have ti: forall k, k <c csucc i -> ~ inc (xv k) c.
     move => k /(cltSleP iN) ki.
     case: (equal_or_not k i) => ki1; first by ue.
     have lki: k <c i by split.
     move => bad; move: (td _ bad); case /setU2_P; first by exact (pc _ lki).
     exact (qc _ lki).
   have tj:forall k, j <c k -> k <c m -> ~ inc (xv k) c.
     move => k jk km bad;  move: (td _ bad); case /setU2_P;
         [by exact (pd _ jk km) | by exact (qd _ (cle_ltT cij jk) km)].
   split => //.
   exists (Lg (Nint m) (fun i => B i i)).
   split => //.
          fprops.
        by aw.
     move => i im; rewrite LgV//; last by apply /NintP.
     have iN: inc i Nat  by apply (NS_le_nat (proj1 im) mN).
     by move: (Bp _ iN _ (cleR (proj31_1 im)) im) => [ok _].
   move => i im; rewrite LgV//;  last by apply /NintP.
   move => t tb; apply /setC_P;split => //; last by move => /in_set0.
   have iN: inc i Nat  by apply (NS_le_nat (proj1 im) mN).
   move: (Bp _ iN _ (cleR (proj31_1 im)) im) => [_ pa _ _ _].
   move: (pa _ tb);case /setU2_P => ti.
     by apply /setUb_P;exists i=> //; rewrite df;  apply /NintP.
   move: (dd _ im) => dr2.
   move: ti => /setUb_P;aw; move => [y yi tv].
   apply /setUb_P ;by  exists y; fprops; move: tv; rewrite LgV.
  move => i im; rewrite LgV; [ move => bad | by apply /NintP].
  have iN: natp i  by apply (NS_le_nat (proj1 im) mN).
  move: (Bp _ iN _ (cleR (proj31_1 im)) im) => [_ pa pb pc pd].
  have pg:sub (Nint m -s1 i) (Nint m).
      by move => t /setC1_P; case.
   have pe: sub (Nint m -s1 i)
        (domain (Lg (Nint m) (fun i0 => B i0 i0))) by aw.
   have pf: fgraph (Lg (Nint m) (fun i0 => B i0 i0)) by fprops.
   move: (bad _ pb) => /setUb_P; aw.
   move => [y ya]; move: (ya) => /setC1_P [ym yi]; rewrite !LgV//.
   move: (ym) =>  /(NintP  mN) ym1.
   have kN: inc y Nat by apply (NS_le_nat (proj1 ym1) mN).
   move: (Bp _ kN _ (cleR (proj31_1 ym1)) ym1) => [_ _ _ qc qd].
   case: (cleT_el (proj31_1 ym1) (proj31_1 im)) => ciy.
        by apply: qd.
     by apply: qc.
move => r m rN mN mnz f B hyp cb.
have fsb: finite_set B by hnf; rewrite cb; apply /NatP.
move: B fsb r m f rN mN hyp cb mnz.
apply: finite_set_induction0.
  move => r m f rb mb Hyp ce mn; apply: ind0 => //.
  have -> //: m = m +c r; rewrite - ce cardinal_set0 Nsum0r //.
move => B x Hrec nxb r m f rN mN h8 cs1 mnz.
move: cs1; rewrite (csucc_pr nxb) => sr.
have rnz: r <> \0c by rewrite - sr; apply: succ_nz.
move: (cpred_pr rN rnz);move: (cpred_pr1 (CS_cardinal B)); rewrite sr => ->.
set r':= cardinal B; move => [r'N rsr'].
have mrN: natp  (m +c r) by fprops.
have mrN': natp (m +c r')  by fprops.
have mrnz: m +c r <> \0c. 
   move: (csum_M0lt  rN mnz); rewrite csumC =>h.
   by move: (cle_ltT (cle0n rN) h) => [_ /nesym].
move: (ind0 _ mrN mrnz _ h8) => [Ap [fgAp dAp Apr sApu sAu]].
move: sApu.
have ->: (unionb f -s emptyset) = unionb f.
   set T:= unionb f; set_extens t; first by move /setC_P => [].
      move => tt; apply /setC_P;split => //; case; case.
move => sApu.
suff: exists g : Set, ppr8_conc R (B +s1 x) Ap g m.
  move => [g [g1 g2 g3 g4 g5]]; exists g;split => //.
  move => i im; move: (g4 _ im) => ts t tg; move: (ts _ tg).
  move /setC_P=> [ta tb]; apply /setC_P;split => //.
  move: ta => /setUb_P  [y yd ty]; apply: (sApu y _ _ ty).
  by move: yd; rewrite dAp => /(NintP mrN).
have ta: m +c r' <=c m +c r. 
  apply: csum_Mlele; fprops; rewrite rsr'; fprops.
case: (inc_or_not x (unionb Ap)) => xu; last first.
  set Ap' := restr Ap (Nint (m +c r')).
  have tb: sub (Nint (m +c r')) (domain Ap).
    rewrite dAp; apply: Nint_M1; fprops.
  have tc: forall i, i<c m+c r' -> Vg Ap' i = Vg Ap i.
     by  move => i ilt; rewrite /Ap' LgV//; apply /(NintP mrN').
  have td: domain Ap' = Nint (m +c r') by rewrite /Ap' restr_d.
  have te: fgraph Ap' by rewrite /Ap'; fprops.
  have h8': ppr8_hyp R Ap' (m +c r').
   split => //.
       move => i im; rewrite (tc _ im); apply: Apr; exact (clt_leT im ta).
     move => i im; rewrite (tc _ im).
     have imr:= (clt_leT im ta).
    move => ns; move: (sAu _ imr); case => t tq.
    have iN: inc i Nat by apply (NS_le_nat (proj1 imr) mrN).
    have tr: sub (Nint i) (domain Ap'). 
     rewrite td; apply: (Nint_M1 mrN' (proj1 im)).
    have ts: sub (Nint (m +c r) -s1 i) (domain Ap).
      by  move => z /setC_P; rewrite dAp; move => []; aw.
    move: (ns _ tq) => /setUb_P;aw.
    move => [y yi]; rewrite LgV// => tv; apply /setUb_P; aw.
   move: yi =>  /(NintP iN) [ti1 ti2].
    have yk: inc y (Nint (m +c r) -s1 i). 
        apply /setC1_P; split => //; apply /(NintP mrN); exact: cle_ltT ti1 imr.
    exists y=> //; rewrite LgV// - tc //; exact: cle_ltT ti1 im.
  move: (Hrec _ _ _ r'N mN h8' (refl_equal r') mnz).
  move => [g [g1 g2 g3 g4 g5]]; exists g;split => //.
  have sa: sub (unionb Ap') (unionb Ap).
    move => t /setUb_P;rewrite td; move => [y yi yv].
    apply /setUb_P; rewrite dAp.
     move: yi => /(NintP mrN') yi; exists y=> //; 
       last by rewrite -(tc _ yi).
     apply /(NintP mrN); exact: (clt_leT yi ta).
  move => i im t tv; move: (g4 _ im _ tv).
  move /setC_P=> [ua ub] => //; apply /setC_P;split;fprops.
  dneg tq; move: tq; case /setU1_P => // tx; case: xu; apply: sa; ue.
move: xu=> /setUb_P; rewrite dAp;move => [ix] /(NintP mrN) ixd xix.
pose swap i := Yo (i = ix) (m +c r') (Yo (i = m +c r') ix i).
have swp2: forall i, swap (swap i) = i.
   move => i; rewrite /swap.
   case: (equal_or_not i ix) => eix; Ytac0.
      Ytac0; Ytac xx; [ue| done].
   by case: (equal_or_not i (m +c r')) => eiy; Ytac0; Ytac0 => //; Ytac0.
have swp3: forall i, i<c m +c r -> swap i <c m +c r.
   move => i ily; rewrite /swap;Ytac le1.
     rewrite (csumC m)(csumC m);apply: csum_Mlteq => //;rewrite rsr'; fprops.
   Ytac le2 => //.
have swp4: forall i, i <c m +c r' -> swap i <> ix.
   move => i [ily nr]; rewrite /swap; Ytac eq1; last by Ytac0.
   by rewrite -eq1; apply:nesym.
have swp5: forall i, i <c m +c r' -> (swap i <c m +c r /\ swap i <> ix).
   move => i ilt; split; [ apply: swp3 (clt_leT ilt ta) | by apply: swp4 ]. 
pose uni i:= (unionb (restr Ap (Nint (m +c r) -s1 i))).
pose xv1 i := rep ((Vg Ap i) -s (uni i)).
have xvp1: forall i, i <c ( m +c r) -> inc (xv1 i) ((Vg Ap i) -s (uni i)).
     move => i im; move: (sAu _ im); rewrite /xv1/uni; set s := unionb _ => ss.
     apply: rep_i; case: (emptyset_dichot (Vg Ap i -s s)) => // ve.
     by move: (empty_setC ve).
have xvp2: forall i, i<c m +c r -> inc (xv1 i) (Vg Ap i).
  by  move => i im; move: (xvp1 _ im) => /setC_P [].
have xvp3: forall i j, i <c m +c r -> j <c m +c r -> i <> j ->
     ~(inc (xv1 i) (Vg Ap j)).
  move => i j ilt jlt ij; move: (xvp1 _ ilt) => /setC_P [_ h]; dneg h1.
  have tb: sub (Nint (m +c r) -s1 i) (domain Ap).
    by rewrite dAp => t /setC_P [].
  have ji: inc j (Nint (m +c r) -s1 i).  
    by  apply /setC1_P;split;fprops; apply /(NintP mrN).
  apply /setUb_P;exists j => //;aw; trivial; rewrite LgV//.
pose Bi i := Yo (inc x (Vg Ap i))(cmr (Vg Ap i) (Vg Ap ix) x (xv1 i)) (Vg Ap i).
have bip: forall i, i<c m +c r -> i <> ix ->
   [/\ inc (Bi i) R , sub (Bi i) (Vg Ap i \cup Vg Ap ix),
     inc (xv1 i) (Bi i) & ~ inc x (Bi i)].
   move => i im nix; rewrite /Bi; Ytac xai.
      have pa: inc x (Vg Ap i \cap Vg Ap ix) by fprops.
      have pb: inc (xv1 i) (Vg Ap i -s Vg Ap ix).
       apply /setC_P;split;fprops; apply: xvp3 => //.
       apply: (cmrp  _ _ _ _ (Apr _ im) (Apr _ ixd) pa pb).
   split;fprops; apply: subsetU2l. 
set Bf := Lg (Nint (m +c r')) (fun z => Bi (swap z)).
have h8': ppr8_hyp R Bf (m +c r').
  rewrite /Bf;split => //.
        fprops.
      by aw.
    move => i im; rewrite LgV; last by apply  /(NintP mrN').
    by move: (swp5 _ im)=> [s1 s2]; move: (bip _ s1 s2) => [ok _].
  move => i im; rewrite LgV; [ move => ns | by apply /NintP].
  move: (swp5 _ im)=> [s1 s2]; move: (bip _ s1 s2) => [p1 p2 p3 p4].
  have iN: inc i Nat by apply (NS_le_nat (proj1 im) mrN').
  have pa:fgraph (Lg (Nint (m +c r')) (fun z => Bi (swap z))).  
    by fprops.
   have pb:  sub (Nint i) (Nint (m +c r')).
     by apply: Nint_M1 => //; move: im =>[].
  move: (ns _ p3)  => /setUb_P [y];rewrite restr_d. 
  move => ya; move: (ya) => /(NintP iN) yi.
  have ph:=(clt_ltT yi im). 
  have ph':=(clt_leT ph ta).
  have pc: inc y (Nint (m +c r')) by apply /NintP.
  rewrite !LgV//; move: (xvp1 _ s1) => /setC_P [_ pd] pe; case: pd.
  have pf: sub (Nint (m +c r) -s1 swap i) (domain Ap).
    by move => t; rewrite dAp => /setC_P [].
  have pg: inc (swap y) (Nint (m +c r) -s1 swap i).
    apply /setC_P; split. 
       apply/(NintP mrN); apply: swp3 => //. 
    move /set1_P; move: yi => [_]; rewrite - {1} (swp2 i) -{1} (swp2 y). 
    by move => h1 h2; case: h1; rewrite h2.
  apply /setUb_P;exists (swap y); aw; bw => //.
  move: (swp5 _ ph)=> [s3 s4]; move: (bip _ s3 s4) => [q1 q2 _].
   move: (q2 _ pe); case /setU2_P;[by exact | move => inc1 ].
   case: (xvp3 (swap i) ix s1 ixd s2 inc1).
move: (Hrec _ _ _ r'N mN h8' (refl_equal r') mnz).
move=> [g [g1 g2 g3 g4 g5]]; exists g;split => //.
move => i im t tv; move: (g4 _ im _ tv) => /setC_P [] /setUb_P [y yd tv1] tN.
move: yd; rewrite /Bf; aw => ym; move: (ym) => /(NintP mrN') ym'.
move: tv1; rewrite /Bf LgV//; move => tv1.
move: (swp5 _ ym')=> [s3 s4]; move: (bip _ s3 s4) => [_ q2 _ q4].
apply /setC_P;split.
   by apply /setUb_P; rewrite dAp; move: (q2 _ tv1); case /setU2_P => h;
   [exists (swap y) | exists ix]=> //; apply /(NintP mrN).
by move /setU1_P => aux; case: tN; case: aux => // tx; case: q4; rewrite -tx.
Qed.


Lemma pure_properties_res9 A R (U := set_of_pure A R):
  mobile_ext R A ->
  (forall x z, inc x R -> inc z R -> sub x z -> z = x) ->
  forall n f B,
    natp n ->
    cardinal B <c n ->
    fgraph f ->  domain f = Nint n ->
    (forall i, i <c n -> sub (Vg f i) A) ->
    (forall i, i <c n -> ~ inc (Vg f i) U) ->
    (forall i, i <c n -> 
      inc ((Vg f i) \cap (unionb (restr f (Nint i)))) U) ->
    ~ (inc ((unionb f) -s B) U).
Proof.
move => mer minr n f B nN cb fgf df fA fnu ifu.
move /set_of_pureP; move => [_ dp].
have aux: forall i, i <c n -> exists2 x, inc x R & sub x (Vg f i).
  move => i idf; move: (fA _ idf) (fnu _ idf) => pa pb.
  ex_middle bad; case: pb; apply/set_of_pureP; split => //.
  by move => X xa xb;case: bad; exists X.
pose Bi i:= choose (fun x => (inc x R /\ sub x (Vg f i))).
have Bip: forall i, i <c n -> (inc (Bi i) R /\ sub (Bi i) (Vg f i)).
   move => i lin; move: (aux _ lin) => [x xa xb].
   have h: exists x , inc x R /\ sub x (Vg f i) by exists x.
   apply: (choose_pr h).
set f':= Lg (Nint n) Bi.
have h8: ppr8_hyp R f' n.
  rewrite /f';split => //.  
        fprops.
      by aw.  
    move => i lin; rewrite LgV//; [by move: (Bip _ lin) =>[] | by apply /NintP].
  move => i lin; rewrite LgV; [ move => sb |  by apply /NintP].
  move:  (Bip _ lin) => [pa _].
  have pc: sub (Bi i) (Vg f i \cap unionb (restr f (Nint i))).
    move => t tb; move: (sb _ tb).
    have sa: fgraph (Lg (Nint n) Bi) by fprops.
    have iN: natp i by apply (NS_le_nat (proj1 lin) nN).
    have sc:sub (Nint i) (Nint n).
      by apply: Nint_M1 => //; move: lin => [].
    have sd: sub (Nint i) (domain (Lg (Nint n) Bi)) by aw.
    have se: sub (Nint i) (domain f) by rewrite df.
    move /setUb_P; aw; move => [y ys]. 
    move: (sc _ ys) => yi; rewrite ! LgV// => tc.
    apply setI2_P;split => //. 
         by move: (Bip _ lin) => [_]; apply.
     apply /setUb_P; exists y; aw; bw => //.
     have yn: y<c n by apply /NintP.
     by move:  (Bip _ yn) => [_]; apply.
  move: (ifu _ lin) => /set_of_pureP [_ pb].
  by move: (pb _ pc); case.
move: (NS_le_nat (proj1 cb) nN) => rN.
move: (cdiff_nz cb). 
move: (cdiff_pr (proj1 cb)).
move: (NS_diff (cardinal B) nN);set m := n -c cardinal B.
rewrite csumC;move=> mN rmn mnz.
rewrite -rmn in h8.
move: (pure_properties_res8 mer minr rN mN mnz h8 (refl_equal (cardinal B))).
move => [g [g1 g2 g3 g4 g5]].
have zm: \0c <c m by  apply:card_ne0_pos; fprops.
move: (g3 _ zm)(g4 _ zm) => ta tb.
case: (dp (Vg g \0c)) => //.
move => t tv; move: (tb _ tv) => /setC_P [sa sb] => //.
move: sa; rewrite /f' => /setUb_P; aw; move => [y yi];rewrite LgV// => tc.
apply /setC_P;split => //;apply /setUb_P; rewrite df; ex_tac.
by move: yi =>  /(NintP nN) yi; move: (Bip _ yi) => [_]; apply.
Qed.

(** Pure sets and max pure sets are (a) there is no pure set, (b) 
   pure sets have cardinal [<=n]; max pure have cardinal [n], (c) 
pure sets are small; max pure are singletons, (d) the only pure set is empty.
*)


Section Exercice4_11.
Variables A R: Set.
Hypothesis mnr: mobile_ext R A.

Lemma Exercise4_11a: 
  inductive (sub_order (set_of_pure A R)). 
Proof. by apply: pure_properties_res1. Qed.

Lemma Exercise4_11b x: sub x A -> pure R x -> 
  exists2 y, sub x y & max_pure A R y.
Proof.
move => xa px.
set po:= (sub_order (set_of_pure A R)).
move: (sub_osr (set_of_pure A R)) => [or sr].
have xsr: inc x (substrate po).
   by rewrite sr; apply: Zo_i => //; apply /setP_P.
move: (inductive_max_greater or Exercise4_11a xsr).
move => [m]; rewrite /po/maximal sr.
move => [mp xm] /sub_gleP [_ _ sm]; move: mp => /set_of_pureP.
move=> [ma prm]; exists m => //; split => // p pp cmp pa; symmetry; apply: xm.  
by apply /sub_gleP;split => //; apply: Zo_i => //; apply /setP_P.
Qed.




(** If  [M] is maximal pure and [x] is not in [M] then  [Ex4_11EM M x] 
   is the unique subset of [M] such that adjoining [x] gives an element of [R]*)

Lemma Exercise4_11c M x: max_pure A R M -> inc x (A -s M) ->
  exists !z, [/\ inc z (\Po A), sub z M & inc (z +s1 x) R].
Proof.
move: mnr => [q1 q2 q3 q4].
move => [pm1 pm2 mpx] /setC_P [xA nxm]. 
apply /unique_existence; split; last first.
  move => a b [aA aM saR] [bA bM sbR].
  ex_middle nab.
  have ne1: ~ inc x a by move => xa; case: nxm; apply: aM.
  have ne2: ~ inc x b by  move => xa; case: nxm; apply: bM.
  have ne3: (a +s1 x) <> (b +s1 x).
    move => eta; case: nab. 
    by rewrite - (setU1_K ne1) - (setU1_K ne2) eta.
  have xc: inc x ((a +s1 x) \cap (b +s1 x)) by fprops.
  move: (q3 _ _ saR sbR ne3 _ xc); move => [Z [Zr sz nxz]].
    have zM: sub Z M.
      move => t tZ; move: (sz _ tZ); case /setU2_P; case /setU1_P; fprops;
      by move => tx; case: nxz; rewrite - tx.
  by case: (pm2 _ zM).
have ta: sub (M +s1 x) A by move => t; case /setU1_P; [ fprops | by move => ->].
have [t ts tr]: exists2 t, sub t (M +s1 x) & inc t R.
  case: (p_or_not_p (pure R (M +s1 x))) => npt.
    case: nxm; rewrite (mpx _ npt (@sub_setU1 M x) ta); fprops.
  by ex_middle bad; case: npt => s ts b3;case: bad; exists s.
move: (sub_trans ts ta) => tA.
set z := t -s1 x.
have zM: sub z M.
  move => s /setC1_P [td te].
  by move: (ts _ td); case /setU1_P.
move: (pm2 _ zM) => zR.
have zt: sub z t by move => u /setC1_P [].
case: (inc_or_not x t) => xy.    
  move: (setC1_K xy) => tc.
  exists z;split => //; first by (apply /setP_P; apply: (sub_trans zt tA)).
  by rewrite /z tc.
case: zR; have -> //: z = t. 
set_extens s; first by move /setC1_P => [].
by move => st; apply /setC1_P;split => //; dneg sx; rewrite - sx.
Qed.

Definition Ex4_11EM M x := select (fun z => (sub z M /\ inc (z +s1 x) R))
  (\Po A).


Lemma Exercise4_11d M x: max_pure A R M -> inc x (A -s M) ->
  (sub (Ex4_11EM M x) M /\ inc ((Ex4_11EM M x) +s1 x) R).
Proof. 
move => pa pb; rewrite /Ex4_11EM.
pose p z := sub z M /\ inc (z +s1 x) R; rewrite -/p -/(p _).
move:(Exercise4_11c pa pb) => [z [[qa qb qc] zb]].
have h:(singl_val2 (inc ^~ (\Po A)) p).
  move => a b aP [r1 r2] bP [r3 r4].  
  by rewrite - (zb _ (And3 aP r1 r2)) (zb _ (And3 bP r3 r4)).
by rewrite - (select_uniq h qa (conj qb qc)).
Qed.

Lemma Exercise4_11e M x: max_pure A R M -> inc x (A -s M) ->
  inc (Ex4_11EM M x +s1 x) (min_incl_r R).
Proof.
move => mm xa.
move: (Exercise4_11d mm xa) => [pa pb]; apply: Zo_i => // t tr ts.
move: (mm) => [m1 m2 m3].
case: (inc_or_not x t) => xt; last first.
  have ta: sub t (Ex4_11EM M x). 
    move => s st; move: (ts _ st); case /setU1_P => // sx; case: xt; ue.
  by move: (m2 _ (sub_trans ta pa) tr).
set x0 := Ex4_11EM M x.
have qa: [/\ inc x0 (\Po A), sub x0 M & inc (x0 +s1 x) R]. 
   rewrite /x0;split => //; apply /setP_P => //; apply: (sub_trans pa m1).
set x1 :=  (t -s1 x).
have ta: t = x1 +s1 x by symmetry;apply:setC1_K.
have tb: sub (t -s1 x) M.
  move => s /setC1_P [sa sb]; move: (ts _ sa); case /setU1_P => //; apply: pa.
have qb: [/\ inc x1 (\Po A), sub x1 M & inc (x1 +s1 x) R]. 
  rewrite /x1;split => //; [by apply /setP_P; apply: (sub_trans tb m1) | ue ].
move /unique_existence: (Exercise4_11c mm xa) => [_ un]. 
by rewrite (un _ _ qa qb).
Qed.
 
Lemma Exercise4_11f M x y: max_pure A R M -> inc x (A -s M) ->
  inc y (Ex4_11EM M x) -> max_pure A R ((M +s1 x) -s1 y).
Proof.
move => mxpm xam ye; move: (Exercise4_11d mxpm xam) => [pa pb].
move: (mxpm) (xam) => [ma pm mpm] /setC_P [xa xm].
set T := ((M +s1 x) -s1 y).
have tpP: forall u, inc u T <->  ((inc u M \/ u = x) /\ u <> y).
  move => u; split. 
   by move /setC1_P =>[sa sb]; split => //; apply /setU1_P.
  by move => [sa sb]; apply /setC1_P;split => //; apply /setU1_P.
have tA: sub T A.  move => t /tpP []; case; [fprops | by  move => ->].
move: mnr => [q1 q2 q3 q4].
split; first by exact.
  move => z zt zr.
  case: (inc_or_not x z) => xz; last first.
    apply: pm zr; move => t tz; move: (zt _ tz) =>  /tpP.
    move => [h _]; case: h => // tx; case: xz; ue.
  have xe: inc x ((Ex4_11EM M x) +s1 x) by fprops.
  have xnez: (Ex4_11EM M x) +s1 x <> z.
    move => ta.
    have : inc y ((Ex4_11EM M x) +s1 x) by fprops.
    by rewrite ta =>yz; move: (zt _ yz) => /tpP [_].
  have xi: inc x ((Ex4_11EM M x) +s1 x \cap z) by fprops.
  move: (q3 _ _  pb zr xnez _ xi); move => [Z [ZR Zt xZ]].
  have ZM: sub Z M.
    move => t tZ;move: (Zt _ tZ); case /setU2_P.
      case /setU1_P; [ by apply: pa | by move => tx; case: xZ; ue].
    move => tz; move: (zt _ tz) => /tpP [ta tb]. 
    case: ta => //;move => tx; case: xZ; ue.
  by case: (pm _ ZM). 
move => p pp sp pA.
case: (inc_or_not y p) => yp.
   have st: sub (M +s1 x) A by  move => t; case /setU1_P; fprops; move => ->.
   have pt: (pure R (M +s1 x)).
     move => s sst; apply: pp.
     move => t ts; case: (equal_or_not t y) => Tp; first by rewrite Tp.
     by apply: sp; apply /tpP;split => //; apply /setU1_P; apply: sst.
   have st1: sub M (M +s1 x) by fprops.
   case: xm; rewrite (mpm _ pt st1); fprops.
ex_middle ntp.
move: (setC_ne (conj sp ntp)) =>[v] /setC_P [vp vT].
have ynv: y <> v by move => yv;case: yp; rewrite yv.
move: (pA _ vp) => vA.
have pt: pure R (T +s1 v).
  have sa: sub (T +s1 v) p by move => t; case /setU1_P;[ apply:sp | move => ->].
  move => b ba; apply: pp;  apply: (sub_trans ba sa).
have nvM: inc v (A -s M). 
    apply /setC_P; split => //; move => vm. 
    by case: vT; apply/tpP;split => //; [ left | apply:nesym ].
have xnv: x <> v by move => xv;case: vT; apply /tpP;split; fprops.
move: (Exercise4_11d mxpm nvM); move => [sE iteR].
set Sx := ((Ex4_11EM M x) +s1 x).
set Sv := ((Ex4_11EM M v) +s1 v).
have s1: sub Sv A by move => t; case /setU1_P; fprops; move => ->.
have s2: sub Sx A by move => t ; case /setU1_P ; fprops; move => ->.
case: (inc_or_not y Sv) => yEv; last first.
  have BM: sub Sv (T +s1 v).
    move => t; case /setU1_P => te; apply/setU1_P; fprops; left.
    apply /tpP; split; first by left; apply: sE.
    dneg ty; apply /setU1_P; left; ue.
  by move: (pt _ BM).  
have yEx: inc y Sx by rewrite /Sx;fprops.
have nSxv: Sx <> Sv.
  dneg sxv; have: inc x Sx by rewrite /Sx; fprops.
  by rewrite sxv /Sv;aw; case /setU1_P => // xv; case: xm; apply: sE.
have yi: inc y (Sx \cap Sv) by fprops.
move: (q3 _ _ pb iteR nSxv _ yi) => [Z [Zr zi nyz]].
have zt: sub Z (T +s1 v).
  move => t tz.
  have tny : t <> y by  move => ty; case: nyz; ue.
  move: (zi _ tz); case /setU2_P; case /setU1_P => ta; apply /setU1_P.
  by left; apply /tpP;split => //; left; apply: pa.
  by left; apply /tpP;split => //; right.
  by left; apply /tpP;split => //; left; apply:sE.
  by right.
by move: (pt _ zt).
Qed.



(** Two maximal pure sets are equipotent. Let [C = M - N].
If [C] is empty, then [M] is a subset of [N] and [M=N]. 
If [C] is finite, we take [a] in [C] and [b] in [ (Ex4_11EM N a) - M] (it 
exists by purity of [M]. Then [ N - a + b] is maximal pure, has the same 
cardinal as [N] and has same cardinal as [M] by induction. *)


Lemma  Exercise4_11g M N: max_pure A R M -> max_pure A R N ->
  finite_set (M -s  N) -> M \Eq N.
Proof.
set C :=  (M -s  N).
have : C = (M -s N) by done.
move: C; move => C cv mp mp' fsc; move: C fsc M N cv mp mp'.
apply: finite_set_induction0.
   move => M M' iz mp mp'.
   symmetry in iz; move: (empty_setC iz) => l1.
   move: mp mp' => [mp0 mp1 mp2] [mp5 mp3 mp4].
   rewrite (mp2 _ mp3 l1 mp5);fprops. 
move => C a Hrec naC M N cv Mp Np.
have : inc a (C +s1 a) by fprops.
rewrite cv; move => /setC_P [aM naN].
have aAN: inc a (A -s N) by apply /setC_P; split => //;apply (proj31 Mp). 
move:(Exercise4_11d Np aAN) => [seN teR].
case: (emptyset_dichot ((Ex4_11EM N a) -s M)) => esd.
  move: (empty_setC esd) => s1.
  have s2: sub  ((Ex4_11EM N a) +s1 a) M 
     by move => t; case /setU1_P; fprops => ->.
  by move: (proj32 Mp _ s2).
move: esd => [b] /setC_P [bt nb].
move: (Exercise4_11f Np aAN bt).
set T :=  ((N +s1 a) -s1 b) => mpT.
have pa: C  = M -s T.
  set_extens t.
    move => tc; apply /setC_P.
    have: inc t (C +s1 a) by fprops.
    rewrite cv => /setC_P [tm tn]; split => //.
    move /setC1_P => [] /setU1_P; case => // ta _;case: naC; ue.
  move => /setC_P  [tm] /setC1_P aux.
  have ntb: t <> b by move=> tb; case: nb; ue.
  case: (equal_or_not t a) => nta. 
     by case: aux; split; [ rewrite nta;fprops | exact].
  case: (inc_or_not t N) => ntN; first by case: aux; split; [ fprops | exact].
  have: inc t (C +s1 a) by rewrite cv; apply /setC_P; split.
  by  case /setU1_P.
apply /card_eqP.
set s := (N +s1 a).
have bs: inc b s by  apply /setU1_P;left; apply: seN.
have ias: inc a s by rewrite /s;fprops.
move: (csucc_pr2 bs) (csucc_pr2 ias).
rewrite (setU1_K naN); move => -> ss.
have ca: cardinalp (cardinal N) by apply: CS_cardinal.
have cb: cardinalp (cardinal (s -s1 b)) by apply: CS_cardinal.
by rewrite - (csucc_inj cb ca ss);apply/card_eqP; apply:Hrec.
Qed.

(** Assume [z] in [M-N] not in the union of [ Ex4_11EM M x] for [x]
  in [N-M]. Let [F = Ex4_11EM N z].
Admitted  *)

Lemma  Exercise4_11h M N:
  max_pure A R M -> max_pure A R N -> 
  sub (M -s N)  (unionb (Lg (N -s M) (fun z => (Ex4_11EM M z)))).
Proof.
move => mp np; move => z zmn; apply setUb_P; aw;ex_middle bad1.
have bad2: forall x, inc x (N -s M) -> ~(inc z (Ex4_11EM M x)).
  move => x xa xb; case: bad1; ex_tac; rewrite LgV//.
move: (zmn) =>  /setC_P[zM zN].
move: (proj31 mp _ zM) => zA.
have zan: inc z (A -s N) by apply /setC_P.
move: (Exercise4_11d np zan) => [F0n F0R].
move: mnr => [q1 q2 q3 q4].

have rec: forall F y, sub F (N \cup M) -> inc (F +s1 z) R ->
  inc y (F -s M) ->  
  exists F', [/\ sub F' (N \cup M), inc (F' +s1 z) R, ~ (inc y F') &
    sub (F' -s M) (F -s M)].
  move => F y FA FpR yFsM.
  move: yFsM => /setC_P [yF yM]; move: (FA _ yF) => yNuM.
  have yN: inc y N by move: yNuM; case /setU2_P.
  have yam: inc y (A -s M) by apply/setC_P; split => //;apply: (proj31 np _ yN).
  move:  (Exercise4_11d mp yam) => [ta tb].
  have nXY: (F +s1 z) <> (Ex4_11EM M y +s1 y).
    move => heq.
    have yNM: inc y (N -s M) by apply /setC_P.
    move: (bad2 _ yNM) => nz.
    have: inc z (F +s1 z) by fprops.
    rewrite heq;case  /setU1_P => // => eq2;case: zN; ue.
  have ti: inc y ((F +s1 z) \cap (Ex4_11EM M y +s1 y)) by fprops.
  move : (q3 _ _  FpR tb nXY _ ti) => [Z [Za Zb Zc]].
  have zd:  sub Z (N \cup M).
    move => t tz; case/setU2_P:(Zb _ tz).
      by case/setU1_P; [ apply: FA | move => ->; apply/setU2_P; right].
    case /setU1_P; move =>h; apply/setU2_P; [by right; apply:ta | left; ue].

Admitted.
(*
move: (Exercise4_11h np zA zN) => [F0n F0R].
have pa: forall x, inc x (N -s M) -> 
  exists y, inc y (M -s N) /\ inc y (Ex4_11EM M x).
  move => x; srw; move => [xN xM].
  move: (proj11 np _ xN) => xA.
  move: (Exercise4_11h mp xA xM) => [ta tb].
  case: (emptyset_dichot ((Ex4_11EM M x) -s N)) => ed.
    move: (empty_complement ed) => sd.
    have sd1: sub (Ex4_11EM M x +s1 x) N by move => t; aw; case;split => // ->.
    by move: (proj12 np _ sd1).
  move: ed => [t]; srw; move=> [t1 t2]; exists t; srw;split => //.
pose f x := choose (fun y => inc y (M -s N) /\ inc y (Ex4_11EM M x)).
have fp: forall x, inc x (N -s M)  -> 
   (inc (f x) (M -s N) /\ inc (f x) (Ex4_11EM M x)).
   by move => x xc; apply choose_pr; apply: pa.

set S :=  (M -s (fun_image (N -s M) f)) \cup (N -s M).
have pb: sub N S.
  move => t tm; rewrite /S; aw.
  case: (inc_or_not t M) => tM; last by right; srw; split => //.
  left; srw; split => //; aw; move => [z]; aw; move => [ta tb].
  move: (fp _ ta); rewrite tb; srw; intuitionxx.
have ps: pure S.
   split. rewrite/S => t;aw; srw; case; move => [ta _].
      apply: (proj11 mp _ ta).
      apply: (proj11 np _ ta).
   move => X Xs Xr.
   admit.  (* wrong ? *)
move: (proj2 np _ ps pb) => ns.
move => t; srw; move=> [tm tn]; bw.
case: (inc_or_not t (fun_image (N -s M) f)).
  aw; move => [z [zc fz]]; move: (fp _ zc) => [ta tb].
  exists z;split => //;bw; ue.
move => xx; case: tn; rewrite ns /S; aw; left; srw;split => //.

Qed.
*)

(** If one complement is finite, then [M] and [N] are equipotent.
Otherwise we use [ Exercise4_11k ] and an upper bound of the cardinal of the 
union. It follows that [ Card(M-N) <= Card(N-M) and vice versa. *)

Lemma  Exercise4_11i M N: max_pure A R M -> max_pure A R N ->
 M \Eq N.
Proof.
move => pM pN.
case: (finite_or_infinite_set (N -s M)) => h1; first by apply:EqS;apply: Exercise4_11g.
case: (finite_or_infinite_set (M -s N))  => h2; first by apply: Exercise4_11g.
move: (Exercise4_11h pM pN) (Exercise4_11h pN pM).
set C1 := (M -s N); set C2 := (N -s M) => s1 s2.
move: (cleT (sub_smaller s1)  (csum_pr1 _)); aw => le1.
move: (cleT (sub_smaller s2)  (csum_pr1 _)); aw => le2.
set f1:= (Lg C2 (fun a : Set => cardinal (Vg (Lg C2 [eta Ex4_11EM M]) a))).
set f2:= (Lg C1 (fun a : Set => cardinal (Vg (Lg C1 [eta Ex4_11EM N]) a))).
have fg1 : fgraph f1 by rewrite /f1; fprops.
have fg2 : fgraph f2 by rewrite /f2; fprops.
have h1': infinite_c (cardinal C2) by  move: h1; move /infinite_setP.
have h2': infinite_c (cardinal C1) by  move: h2; move /infinite_setP.
have cd1: cardinal (domain f1) <=c cardinal C2 by rewrite /f1; aw; fprops.
have cd2: cardinal (domain f2) <=c cardinal C1 by rewrite /f2; aw; fprops.
move: mnr => [q1 q2 q3 q4].
have l1: (forall i, inc i (domain f1) -> Vg f1 i <=c cardinal C2).
   rewrite /f1; aw; move => i idf; rewrite !LgV//; apply: cle_fin_inf => //.
   move: idf  => /setC_P[i1 i2].
   have i3: inc i (A -s M) by apply /setC_P;split => //;apply: (proj31 pN _ i1).
   move: (Exercise4_11d pM i3) => [ _ tf].
   move: (q2 _ tf);  apply: sub_finite_set; fprops.
have l2: (forall i, inc i (domain f2) -> Vg f2 i <=c cardinal C1).
   rewrite /f2; aw. move => i idf; rewrite !LgV//; apply: cle_fin_inf => //.
   move: idf => /setC_P [i1 i2].
   have i3: inc i (A -s N) by apply /setC_P;split => //; apply:(proj31 pM _ i1).
   move: (Exercise4_11d pN i3) => [ _ tf].
   move: (q2 _ tf);  apply: sub_finite_set; fprops.
move: (cleT le1 (notbig_family_sum h1' cd1 l1)) => l3.
move: (cleT le2 (notbig_family_sum h2' cd2 l2)) => l4.
apply/card_eqP;  apply: cardinal_setC3; exact: (cleA l3 l4). 
Qed.


End Exercice4_11.

End Exercise4.
Export Exercise4.
