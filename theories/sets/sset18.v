(** * Theory of Sets  EIV  Structures
  Copyright INRIA (2009-2013 2108) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: sset18.v,v 1.8 2018/09/04 07:58:00 grimm Exp $ *)

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset10.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Example of a group structure *)

Module StructureAux.
 



Definition slistp f := fgraph f /\ natp (domain f).

Definition slength f := domain f.

Definition slistpl f n := slistp f /\ slength f = n.

Lemma slist_domain X: slistp X -> domain X = Nint (slength X).
Proof. 
by  move => [_ nN]; rewrite /slength (NintE nN).  
Qed.

Lemma slength_nat X:  slistp X -> natp (slength X).
Proof. by move => [_ nN].  Qed.

Lemma slist_domainP  X: slistp X ->
  forall i, (inc i (domain X) <-> i <c (slength X)).
Proof. by move=> [_ h] i; apply: iff_sym;apply/(NltP h). Qed.

Definition slist_E f E := slistp f /\ sub (range f) E.
Definition Vl l x := Vg l (cpred x).  

Lemma Vl_correct l i: cardinalp i ->  Vg l i = Vl l (csucc i).
Proof.
by move => ic;rewrite /Vl  cpred_pr1.
Qed.
  
Lemma slist_extent f g :
  slistp f -> slistp g -> slength f = slength g ->
  (forall i, \1c <=c i -> i <=c slength f ->
      (Vl f i = Vl g i))
  -> f = g. 
Proof.
move => fl gl eq1 sv.
have sd: domain f = domain g by rewrite (slist_domain fl) (slist_domain gl) eq1.
have dp:= (slist_domainP fl).
have nN:= (slength_nat fl).
move: fl gl =>  [ha _] [ha' _].
apply:fgraph_exten => // i /dp id.  
have ic:=(proj31_1 id).
rewrite (Vl_correct f ic) (Vl_correct g ic).
apply: sv; first by rewrite - succ_zero; apply: cleSS; apply:cle0x.
by apply /(cleSlt0P ic).
Qed.


Lemma Vl_p1 f E x : slist_E f E -> \1c <=c x -> x <=c (slength f) ->
  inc (Vl f x) E.
Proof.
move => [ha hb] hc hd; move: (ha) => [he _].
apply: hb; apply/(range_gP he).
have nN:= (slength_nat ha).
case: (equal_or_not x \0c) => xz; first by move: (cltNge clt_01); rewrite - xz.
move: (cpred_pr  (NS_le_nat hd nN) xz) => [sa sb].
exists (cpred x) => //; apply /(slist_domainP ha).
by apply/(cleSlt0P (CS_nat sa) nN); rewrite - sb.
Qed.



(** Extension of mappings *)


Lemma cpred_pr6' k i:  natp k -> \1c <=c i -> i <=c k ->
    [/\ natp (cpred i), i = csucc (cpred i) & cpred i <c k ].
Proof.
move => sa sb sc.
have w:= clt_01.
have knz: k <> \0c by move => kz; move:(cleT sb sc); rewrite kz; apply:cltNge.
move: (cpred_pr sa knz) =>[ka kb]; move: sc;rewrite kb => sc.
move: (cpred_pr6 ka sb sc) => [pa pb /(cltSleP ka) pc]; split => //.
Qed.

End StructureAux.

Export StructureAux.



Module StructureExample.

Section Preparation.

Definition Law s E := [/\ sub s ((E \times E) \times E),
                       fgraph s & domain s = (E \times E)].
Definition VL s a b := Vg s (J a b).

Lemma Law_in s E a b: Law s E -> inc a E -> inc b E ->
  inc (J (J a b) (VL s a b)) s.
Proof.
by move => [ha hb hc] aE bE; apply: (fdomain_pr1 hb); rewrite hc; apply:setXp_i.
Qed.

Lemma Law_range s E a b: Law s E -> inc a E -> inc b E ->
   inc (VL s a b) E.
Proof.
move => [ha hb hc] aE bE; rewrite /VL.
have pdf: inc (J a b) (domain s) by rewrite hc; apply:setXp_i.
by move: (inc_V_range hb pdf) => /funI_P [z /ha /setX_P [ _ _ qb] ->].
Qed.

Lemma Law_val s E a b c: Law s E -> inc (J (J a b) c) s ->
   c = (VL s a b).
Proof.
by move => [ha hb hc] hd; move: (pr2_V  hb hd); aw.
Qed.

Definition GE_I E := Zo (E\times E) (fun z => P z = Q z).
Definition GE_J E :=
  Zo (((E\times E) \times E)\times (E\times (E\times E)))
     (fun x => [/\ P (P (P x)) = P (Q x),
                   Q (P (P x)) = P (Q (Q x)) &
                   Q (P x) = Q (Q (Q x))]).



Lemma GE_I_incP E x: inc x (GE_I E) <-> [/\ pairp x, P x = Q x & inc (P x) E]. 
Proof.
split.
  by move =>/Zo_P [/setX_P [ha hb hc] hd]; split.
by move => [pa pb pc]; apply:Zo_i => //; apply: setX_i => //; rewrite - pb.
Qed.

Lemma GE_I_fgraph E : fgraph (GE_I E).
Proof.
split; first by move => x /GE_I_incP [].
move => x y  /GE_I_incP [ha hb hc] /GE_I_incP [ha' hb' hc'] sp.
by rewrite - ha -ha' -hb -hb' sp.
Qed.

Lemma GE_I_domain E : domain (GE_I E) = E.
Proof.
apply: extensionality => x.
  by move /funI_P => [z / GE_I_incP [_ _ h] ->].
move=> xe;apply/funI_P; exists (J x x); aw;trivial; apply/GE_I_incP; aw.
split => //; apply: pair_is_pair.
Qed.


Lemma GE_I_range E : range (GE_I E) = E.
Proof.
apply: extensionality => x.
  by move /funI_P => [z / GE_I_incP [_  <- h] ->].
move=> xe;apply/funI_P; exists (J x x); aw; trivial;apply/GE_I_incP; aw.
split => //; apply: pair_is_pair.
Qed.

Lemma GE_I_Ev E x: inc x E -> Vg (GE_I E) x = x.
Proof.
move => xE. 
have : inc (J x x) (GE_I E) by apply/GE_I_incP; saw; fprops.
by move/(pr2_V (GE_I_fgraph E)); aw.
Qed.


Lemma GE_J_P E x: inc x  (GE_J E) <-> exists a b c,
  [/\ inc a E, inc b E, inc c E &  x = (J (J (J a b) c) (J a (J b c)))].
Proof.
split.
  move /Zo_P => [/setX_P]. 
  move => [h1 /setX_P[h2 /setX_P[h3 h4 h5] h6] /setX_P[h7 h8 /setX_P[h9 _ _]]].
  move => [ra rb rc].
  exists (P (P (P x))), (Q (P (P x))), (Q (P x)); split => //.
  by rewrite h3 h2 ra rb rc h9 h7 h1.
move=> [a [b [c [ sa sb sc ->]]] ]; apply /Zo_P; split; aw => //.
by apply:setXp_i; apply: setXp_i => //; apply: setXp_i.
Qed.


Lemma GE_J_fgraph E : fgraph (GE_J E).
Proof.
split; first by move => x /GE_J_P [a [b [c [_ _ _ ->]]]]; fprops.
move => x y  /GE_J_P [a [b [c [_ _ _ ->]]]]/GE_J_P [a' [b' [c' [_ _ _ ->]]]].
by aw => ea;rewrite (pr2_def ea) (pr1_def (pr1_def ea)) (pr2_def (pr1_def ea)). 
Qed.

Lemma GE_J_domain E : domain (GE_J E) = (E\times E) \times E.
Proof.
apply: extensionality => x.
  move /funI_P => [z /GE_J_P [a [b [c [ha hb hc eq]]]] ->].
  by rewrite eq pr1_pair; apply: setXp_i => //; apply: setXp_i.
move=> /setX_P [pa /setX_P[pb pc pd] pe]; apply/funI_P.
exists (J x (J (P (P x)) (J (Q (P x)) (Q x)))); aw; trivial.
by rewrite - {1} pa - {1} pb; apply/GE_J_P; exists (P (P x)), (Q (P x)), (Q x).
Qed.


Lemma GE_J_range E : range (GE_J E) = (E\times (E\times E)).
Proof.
apply: extensionality => x.
  move /funI_P => [z /GE_J_P [a [b [c [ha hb hc eq]]]] ->].
  by rewrite eq pr2_pair; apply: setXp_i => //; apply: setXp_i.
move=> /setX_P [pa pe /setX_P[pb pc pd]]; apply/funI_P.
exists (J (J (J (P x) (P (Q x))) (Q (Q x))) x); aw; trivial.
by rewrite - {4} pa - {3} pb;apply/GE_J_P; exists (P x),(P (Q x)), (Q (Q x)).
Qed.


Lemma GE_J_Ev E a b c: inc a E -> inc b E -> inc c E ->
  Vg (GE_J E) (J (J a b) c) =  (J a (J b c)).
Proof.
move => aE bE cE.
have: inc (J (J (J a b) c) (J a (J b c))) (GE_J E).
  by apply/GE_J_P; exists a,b,c.
by move /(pr2_V(GE_J_fgraph E)); aw.
Qed.



Definition Sprod A B :=
  Zo (((domain A) \times (domain B)) \times (range A \times (range B)))
     (fun z => inc (J (P (P z)) (P (Q z))) A /\ inc (J (Q (P z)) (Q (Q z))) B).

Lemma Sprod_P A B x: inc x (Sprod A B) <-> exists a1 b1 a2 b2,
  [/\ inc (J a1 a2) A, inc (J b1 b2) B & x = J (J a1 b1) (J a2 b2)].
Proof.
split.
  move => /Zo_P.
  set a := P (P x); set b := P (Q x); set c := Q (P x); set d := Q (Q x). 
  move => [h1 [h2 h3]]; exists a,c,b,d; split => //.
  move/setX_P: h1 => [r1 /setX_P[r2 _ _] /setX_P [r3 _ _]].
  by rewrite - r1 -r2 - r3.
move => [a1 [a2 [b1 [b2 [ha hb ->]]]]].
apply:Zo_i; last by aw.
apply: setXp_i; apply:setXp_i; apply/funI_P.
- by exists (J a1 b1); aw.
- by exists (J a2 b2); aw. 
- by exists (J a1 b1); aw. 
- by exists (J a2 b2); aw. 
Qed.

Lemma Sprod_Il E B x: inc x (Sprod (GE_I E) B) <->
  [/\ pairp x, pairp (P x), pairp (Q x), P (P x) = P (Q x)
      & inc (P (P x)) E /\ inc (J (Q (P x)) (Q (Q x))) B].
Proof.
split.
  move/Sprod_P => [a1 [a2 [b1 [b2 [r1 r2 ->]]]]].
  move/GE_I_incP: r1; aw; move => [_ r3 r4];split; fprops.
move=> [h1 h2 h3 h4 [h5 h6]]; rewrite -h1 - h2 - h3; apply /Sprod_P.
exists (P (P x)), (Q (P x)), (P (Q x)), (Q (Q x)); split => //.
apply/GE_I_incP; split; aww.                          
Qed.

Lemma Sprod_Ir A E x: inc x (Sprod A (GE_I E)) <->
  [/\ pairp x, pairp (P x), pairp (Q x), Q (P x) = Q (Q x)
      & inc (Q (P x)) E /\ inc (J (P (P x)) (P (Q x))) A].
Proof.
split.
  move/Sprod_P => [a1 [a2 [b1 [b2 [r1 r2 ->]]]]].
  move/GE_I_incP: r2; aw; move => [_ r3 r4];split; fprops.
move=> [h1 h2 h3 h4 [h5 h6]]; rewrite -h1 - h2 - h3; apply/Sprod_P.
exists (P (P x)), (Q (P x)), (P (Q x)), (Q (Q x)); split => //.
apply/GE_I_incP; split; aww.
Qed.

Lemma Sprod_fgraph A B: fgraph A -> fgraph B -> fgraph (Sprod A B).
Proof.
move => [ha hb] [hc hd]; split.
  by move => x /Sprod_P [a [b [c [d [_ _ ->]]]]]; fprops.
move => x y / Sprod_P[a [b [c [d [pa pb ->]]]]]
          /Sprod_P [a' [b' [c' [d' [pc pd ->]]]]].
aw => eq1;  rewrite - eq1.
move: (hb _ _ pa pc); aw => ea; rewrite - (pr2_def (ea (pr1_def eq1))).
by move: (hd _ _ pb pd); aw => eb; rewrite - (pr2_def (eb (pr2_def eq1))).
Qed.  

Lemma Sprod_domain A B: sgraph A -> sgraph B ->
   (domain (Sprod A B)) = ((domain A) \times (domain B)).
Proof.
move => ga gb.
apply: extensionality.
  move => x /funI_P [z /Sprod_P [a [b [c [d [ha hb hc]]]]] ->].
  by rewrite hc pr1_pair; apply: setXp_i; apply /funI_P; ex_tac; aw.
move => x /setX_P [pp /funI_P[ a hb hc] /funI_P [b he hf]].
apply/funI_P; exists (J x (J (Q a) (Q b))); aw; trivial.
rewrite - pp hc hf; apply /Sprod_P.
exists (P a), (P b), (Q a), (Q b); split => //.
- by rewrite (ga _ hb).
- by rewrite (gb _ he).
Qed.


Lemma Sprod_range A B: sgraph A -> sgraph B ->
   (range (Sprod A B)) = ((range A) \times (range B)).
Proof.
move => ga gb.
apply: extensionality.
  move => x /funI_P [z /Sprod_P [a [b [c [d [ha hb hc]]]]] ->].
  by rewrite hc pr2_pair; apply: setXp_i; apply /funI_P; ex_tac; aw.
move => x /setX_P [pp /funI_P[ a hb hc] /funI_P [b he hf]].
apply/funI_P; exists (J (J (P a) (P b)) x); aw; trivial.
rewrite - pp hc hf; apply/Sprod_P.
exists (P a), (P b), (Q a), (Q b); split => //.
- by rewrite (ga _ hb).
- by rewrite (gb _ he).
Qed.

Lemma Sprod_case1 s E x (f := s \cg (Sprod s (GE_I E))):
  sub s ((E \times E) \times E) ->
  (inc x f <-> exists a b c d t,
                 [/\ x = J (J (J a b) c) d,
                  inc (J (J t c) d) s & inc (J (J a b) t) s]).
Proof.
move => sp.
split.
  move/compg_P => [pa [y ya yb]].
  move /Sprod_Ir: ya;aw; move => [_ pb yc yd [ye yf]]. 
  have ppc: pairp (P (P x)) by move:(sp _ yf) => /setXp_P [/setX_P []].
  exists (P (P (P x))), (Q (P (P x))), (Q (P x)), (Q x), (P y).
  by rewrite ppc pb pa yd yc.
move => [a [b [c [d [t [ha hb hc]]]]]].
have px: pairp x by rewrite ha;fprops.
have ra: inc (J (J t c) (Q x)) s by rewrite ha; aw.
have cE: inc c E by move:(sp _ ra)  => /setXp_P [/setX_P []]; aw.
apply/compg_P; split => //; exists (J t c) => //. 
apply/Sprod_Ir; rewrite ha;aw; split;fprops.
Qed.


Lemma Sprod_case_l1 s E x (f := s \cg (Sprod s (GE_I E))):
  Law s E ->
  (inc x f <-> exists a b c, [/\ inc a E, inc b E, inc c E &
                 x = J (J (J a b) c) (VL s (VL s a b) c) ]).
Proof.
move => ll; move: (ll)=> [sE _ _].
split.
  move /(Sprod_case1 _ sE) => [a [b [c [d [t [ha hb hc]]]]]].
  exists a,b,c.
  move: (sE _ hc) => /setXp_P [/setXp_P [aE bE]] _.
  move: (sE _ hb) => /setXp_P [ /setXp_P [tE cE] dE]. 
  by split => //; rewrite ha (Law_val ll hb) (Law_val ll hc).
move => [a [b [c [aE bE cE ->]]]].
apply/(Sprod_case1 _ sE).
exists a,b,c, (VL s (VL s a b) c),  (VL s a b); split => //. 
  apply: (Law_in ll (Law_range ll aE bE) cE).
apply: (Law_in ll aE bE).
Qed.

Lemma Sprod_case2 s E : Law s E ->
   s \cg (Sprod s (GE_I E)) = fun_image ((E\times E) \times E)
        (fun z=> J z  (VL s (VL s (P (P z)) (Q (P z))) (Q z))).
Proof.
move => h.
apply:extensionality => x.
  move /(Sprod_case_l1 _ h) => [a [b [c [aE bE cE]]] ->].
  apply/funI_P; exists (J (J a b) c); aw;trivial. 
  by apply:setXp_i => //; apply:setXp_i.
move => /funI_P [z /setX_P[pz /setX_P [ppz ha hb] hc] ->].
apply/(Sprod_case_l1 _ h); exists  (P (P z)),  (Q (P z)), (Q z).
by rewrite ppz pz.
Qed.


Lemma Sprod_case3 s E x (f := s \cg (Sprod (GE_I E) s)):
  sub s ((E \times E) \times E) ->
  (inc x f <-> exists a b c d t,
                 [/\ x =  J (J a (J b c)) d,
                  inc (J (J a t) d) s & inc (J (J b c) t) s]).
Proof.
move => sp;split.
  move/compg_P => [pa [y ya yb]].
  move /Sprod_Il: ya;aw; move => [_ pb yc yd [ye yf]]. 
  have ppc: pairp (Q (P x)) by move:(sp _ yf) => /setXp_P [/setX_P []].
  exists (P (P x)), (P (Q (P x))), (Q (Q (P x))), (Q x), (Q y).
  by rewrite ppc pb pa yd yc.
move => [a [b [c [d [t [ha hb hc]]]]]].
have px: pairp x by rewrite ha;fprops.
have ra: inc (J (J a t) (Q x)) s by rewrite ha; aw.
have aE: inc a E by move:(sp _ ra)  => /setXp_P [/setX_P []]; aw.
apply/compg_P; split => //; exists (J a t) => //. 
apply/Sprod_Il; rewrite ha;aw; split;fprops.
Qed.

Lemma Sprod_case4 s E x (f := (s \cg (Sprod (GE_I E) s)) \cg (GE_J E)):
  sub s ((E \times E) \times E) ->
  (inc x f <-> exists a b c d t,
                 [/\ x = J (J (J a b) c) d,
                  inc (J (J a t) d) s & inc (J (J b c) t) s]).
Proof.
move => h; split.
  move => /Zo_P [/setX_P [ha hb hc]] [y hd he].
  move /GE_J_P: hd => [u [v [w [uE vE wE]]]] => eqa.
  move:(pr1_def eqa) (pr2_def eqa) => eqb eqc.
  move/(Sprod_case3 _ h): he => [a [b [c [d [t [eqd ra rb]]]]]].
  move:(pr1_def eqd) (pr2_def eqd) => eqe eqf.
  rewrite eqe in eqc.
  have av:=(pr1_def eqc).
  have bv:=(pr1_def (pr2_def eqc)).
  have cv:=(pr2_def (pr2_def eqc)).
  by exists a,b,c,d,t; split => //; rewrite av bv cv - eqb - eqf ha.
move => [a [b [c [d [t [xv ha hb]]]]]].
move/setXp_P:(h _ hb) => [/setXp_P [bE cE] tE].
move/setXp_P:(h _ ha) => [/setXp_P [aE _] dE].
have ra: inc (J (J a b) c) (domain (GE_J E)).
  by rewrite GE_J_domain; apply: setXp_i => //; apply:setXp_i.
have rb: inc d (range (s \cg Sprod (GE_I E) s)).
  apply/funI_P; exists (J (J a (J b c))  d); aw;trivial.
  by apply/(Sprod_case3 _ h); exists a,b,c,d,t. 
have rc: inc x (domain (GE_J E) \times range (s \cg Sprod (GE_I E) s)).
  by rewrite xv;apply: setXp_i.
apply:(Zo_i rc);exists (J a (J b c)).
  by rewrite xv; aw; apply /GE_J_P;  exists a,b,c.
apply/(Sprod_case3 _ h).
by exists a,b,c,(Q x),t; split => //; rewrite xv;aw.
Qed.

Lemma Sprod_case_l2 s E x (f := (s \cg (Sprod (GE_I E) s)) \cg (GE_J E)):
  Law s E ->
  (inc x f <-> exists a b c, [/\ inc a E, inc b E, inc c E &
                 x = J (J (J a b) c) (VL s a (VL s b c)) ]).
Proof.
move => ll; move: (ll)=> [sE _ _].
split.
  move /(Sprod_case4 _ sE) => [a [b [c [d [t [ha hb hc]]]]]].
  exists a,b,c.
  move: (sE _ hc) => /setXp_P [ /setXp_P [bE cE ] tE]. 
  move: (sE _ hb) => /setXp_P [ /setXp_P [ aE _] dE].
  by split => //; rewrite ha (Law_val ll hb) (Law_val ll hc).
move => [a [b [c [aE bE cE ->]]]].
apply/(Sprod_case4 _ sE).
exists a,b,c, (VL s a (VL s b c)),(VL s b c); split => //.
  apply: (Law_in ll aE (Law_range ll bE cE)).
apply: (Law_in ll bE cE).
Qed.

Lemma Bourbaki_assoc s E : Law s E ->
  ( (s \cg (Sprod s (GE_I E))) = ((s \cg (Sprod (GE_I E) s)) \cg (GE_J E)) 
  <->  forall a b c, inc a E -> inc b E -> inc c E ->
        VL s a (VL s b c) =  VL s (VL s a b) c).
Proof.
move => h; split.
  move => h1 a b c aE bE cE.
  have: inc (J (J (J a b) c) (VL s (VL s a b) c)) (s \cg Sprod s (GE_I E)).
    by apply/(Sprod_case_l1 _ h); exists a,b,c.
  rewrite h1;move/(Sprod_case_l2 _ h) =>[a' [b' [c' [_ _ _ ea]]]].
  rewrite (pr2_def ea); move: (pr1_def ea) => eb.
  rewrite (pr2_def eb); move: (pr1_def eb) => ec.
  by rewrite (pr1_def ec) (pr2_def ec).
move => h';  apply:extensionality => x.
  move/(Sprod_case_l1 _ h) => [a [b [c [aE bE cE ->]]]].
  by rewrite - h' //; apply/(Sprod_case_l2 _ h); exists a,b,c.
move/(Sprod_case_l2 _ h) => [a [b [c [aE bE cE ->]]]].
by rewrite h' //; apply/(Sprod_case_l1 _ h); exists a,b,c.
Qed.

End Preparation.

Section GroupExample.

Definition GT E s := inc s (\Po ((E\times E) \times E)).
Definition GL E s :=
  (forall a b, inc a E -> inc b E -> exists c, inc (J (J a b) c) s) 
  /\ (forall a b, inc a s -> inc b s -> P a = P b -> a = b).   

Definition is_law E f :=  forall x y, inc x E -> inc y E -> inc (f x y) E.

Definition Op E f := Lg (E\times E) (fun z => f (P z) (Q z)).
Definition Opfun E f := Lf (fun z => (f (P z) (Q z)))  (E \times E) E.


Lemma GEl_prop1 E f: is_law E f -> function_prop (Opfun E f) (E\times E) E.
Proof.
rewrite /Opfun => Ho; saw; apply:lf_function => x /setX_P [pa pb pc]. 
by apply: Ho.
Qed.
  
Lemma GEl_prop2 E f: Op E f = graph (Opfun E f).
Proof. by rewrite /Opfun /Lf; aw. Qed.
 
Lemma GEl_prop3 E f: is_law E f -> GT E (Op E f).
Proof.
move => Ho; apply /setP_P => x /funI_P [z zp ->]; apply: setXp_i => //.
by move/setX_P: zp => [ha hb hc]; apply:Ho.
Qed.

Lemma GEl_prop4 E f: is_law E f -> GL E (Op E f).
Proof.
move => H; split => a b ha hb.
  exists (f a b).
  have ->: (f a b) = f (P (J a b)) (Q (J a b)) by aw.
  rewrite /Op; apply: Lg_i; fprops.
move/funI_P:ha => [z ze ->].
by move/funI_P:hb => [z' ze' ->]; aw => ->.
Qed.

Definition transport s g := 
  fun_image s (fun x => J (J (Vf g (P (P x))) (Vf g (Q (P x)))) (Vf g (Q x))).

Lemma transport_p1 E F s g:  GT E s -> bijection_prop g E F ->
   GT F (transport s g).
Proof.
move => /setP_P sp [[[fg _] _] sg tg].
apply/setP_P => t /funI_P [z zs ->].
move/setX_P: (sp _ zs) => [pz /setX_P[pp pp1 pp2] qz].
apply:setXp_i; [ apply:setXp_i; Wtac | Wtac].
Qed.

Lemma transport_p2 E s: GT E s -> (transport s (identity E)) = s.
Proof.
move => /setP_P sp.
set_extens t.
  move/funI_P => [z zs ->].
  move/setX_P: (sp _ zs) => [pz /setX_P[pp pp1 pp2] qz].
  by rewrite ! idV // pp pz.
move => ts; move/setX_P: (sp _ ts) => [pz /setX_P[pp pp1 pp2] qz].
by apply/funI_P; ex_tac; rewrite ! idV //  pp pz.
Qed.

Lemma transport_p3 E F G s g h: GT E s ->
   bijection_prop g E F -> bijection_prop h F G->
   transport (transport s g) h = transport s (h \co g).
Proof.
move => /setP_P sp [[[fg _] _] sg tg]  [[[fh _] _] sh th].
have xop: h \coP g by  split => //; ue.
set_extens t.
  move/funI_P => [z /funI_P [u us ->] ->]; aw.
  move/setX_P: (sp _ us) => [pz /setX_P[pp pp1 pp2] qz].
  apply/funI_P; ex_tac; rewrite !compfV //; ue.
move => /funI_P [z zs ->].
move/setX_P: (sp _ zs) => [pz /setX_P[pp pp1 pp2] qz].
rewrite !compfV//; try ue; apply/funI_P.
exists (J (J (Vf g (P (P z))) (Vf g (Q (P z)))) (Vf g (Q z))); aw; trivial.
apply/funI_P; ex_tac.
Qed.
  
Definition transportable R:=
  forall E F s g, bijection_prop g E F -> GT E s ->
   (R E s <-> R F (transport s g)).

Lemma transportable_GT: transportable GT.
Proof.
move => E F s g bg te; split => // _; apply:(transport_p1 te bg).
Qed.  


Lemma transportable_GL: transportable GL.
Proof.
move => E F s g [[[fg gi] [_ gs]] sg tg] /setP_P sp.
rewrite sg in gi gs; rewrite tg in gs.
split; move =>[ha hb]; split.
- move => a b aF bF; move: (gs a aF)  (gs b bF) => [a' a'E av] [b' b'E bv].
  move:(ha _ _ a'E b'E) => [c' h].
  by exists (Vf g c'); apply/funI_P; ex_tac; aw; rewrite - av - bv.
- move => a b /funI_P [u us ->] /funI_P [v vs ->]; aw => eq.
  move/setX_P: (sp _ us) => [pz /setX_P[pp pp1 pp2] qz].
  move/setX_P: (sp _ vs) => [pz' /setX_P[pp' pp1' pp2'] qz'].
  move: (gi _ _ pp1 pp1' (pr1_def eq)) => eq1.
  move: (gi _ _ pp2 pp2' (pr2_def eq)) => eq2.
  have eq3: P u = P v by rewrite - pp - pp' eq1 eq2.
  by rewrite (hb _ _ us vs eq3).
- move => a b aE bE.
  move: (Vf_target fg); rewrite sg tg => H.
  move: (ha _ _ (H _ aE) (H _ bE)) => [c /funI_P [z zs zv]].
  exists (Q z).
  move/setX_P: (sp _ zs) => [pz /setX_P[pp pp1 pp2] qz].
  rewrite (gi _ _ aE pp1 (pr1_def (pr1_def zv))).
  by rewrite (gi _ _ bE pp2 (pr2_def (pr1_def zv))) pp pz.
- move => a b ias ibs spab.
  set u := (J (J (Vf g (P (P a))) (Vf g (Q (P a)))) (Vf g (Q a))).
  set v :=  (J (J (Vf g (P (P b))) (Vf g (Q (P b)))) (Vf g (Q b))).
  have r1: inc u (transport s g) by apply/funI_P; exists a.
  have r2: inc v (transport s g) by apply/funI_P; exists b.
  have puv:  P u = P v by rewrite /u/v spab; aw.
  move:(hb _ _ r1 r2 puv); rewrite /u/v => /pr2_def eq.
  move/setX_P: (sp _ ias) => [pz /setX_P[pp pp1 pp2] qz].
  move/setX_P: (sp _ ibs) => [pz' /setX_P[pp' pp1' pp2'] qz'].
  apply: pair_exten => //; apply:(gi _ _ qz qz' eq).
Qed. 

Lemma GE_prop1 E s a: GT E s -> inc a s ->
  [/\ pairp a, pairp (P a), inc (P (P a)) E, inc (Q (P a)) E & inc (Q a) E].
Proof.
move /setP_P => ha hb.
by move: (ha _ hb) => /setX_P [ra /setX_P[rb rc rd] re].
Qed.

Lemma GE_prop2 E s : GT E s -> GL E s -> Law s E.
Proof.
move => ti  [r1a r1b]; split.
- by apply /setP_P. 
- by split => //; move => a /(GE_prop1 ti) [].
- apply: extensionality => x.
    move/funI_P => [z zs ->]; move: (GE_prop1 ti zs) => [_ h2 h3 h4 _].
    by rewrite -h2;apply: setXp_i.
  move/setX_P => [ha hb hc].
  apply/funI_P; move: (r1a _ _ hb hc) => [c]; rewrite ha => zz.
  by exists  (J x c) => //; aw.
Qed.

Lemma GE_prop2_stable E s : GT E s -> GL E s ->
  forall a b, inc a E -> inc b E -> inc (VL s a b) E.
Proof.
move => ha hb; move: (GE_prop2 ha hb) => hc.
move => a b aE bE.
exact:(Law_range hc aE bE).
Qed.
  
Lemma GE_prop3 E s (f := VL s) :  GT E s -> GL E s ->
               is_law E f /\ (Op E f) = s.
Proof.
move => type l1.
have ll:= (GE_prop2 type l1).
have ha: is_law E f by move => x y xE yE; apply:  Law_range.
split => //; apply: fgraph_exten.
- rewrite/Op; fprops.
- by case:ll.
- case:ll =>  _ _ ->; rewrite /Op; aw; trivial.
- by rewrite /Op /f /VL Lgd => x xp; rewrite LgV// (setX_pair xp).
Qed.


Lemma transport_op E F g s: bijection_prop g E F -> GT E s ->  GL E s ->
   forall a b, inc a E -> inc b E ->
    Vf g (VL s a b) = VL (transport s g) (Vf g a) (Vf g b).
Proof.                                   
move => bg te law a b aE bE.
move:(GE_prop2 te law) => law1.
move/(transportable_GT bg te): (te) => typF.
move/(transportable_GL bg te): law => lawF.
move:(GE_prop2 typF lawF) => law2.
apply: (Law_val law2); apply/funI_P.
exists (J (J a b) (VL s a b)); [ by apply:(Law_in law1) | by aw ].
Qed.

Definition GA E s:= 
   s \cg (Sprod s (GE_I E)) = (s \cg (Sprod (GE_I E) s)) \cg (GE_J E).

Lemma GE_prop4 E s  (f := VL s): GT E s -> GL E s ->
   (GA E s <-> forall a b c,
   inc a E -> inc b E -> inc c E -> f a (f b c) =  f (f a b) c).
Proof.
move => ti la.
exact: (Bourbaki_assoc (GE_prop2 ti la)).
Qed.  

Lemma transportable_GA: transportable (fun E s => GL E s /\ GA E s).
Proof.
move => E F s g bg typ.
have ra :=(transportable_GT bg typ).
have rb :=(transportable_GL bg typ).
move:(bg) => [[[fg gi] [_ gs]] sg tg].
rewrite sg in gi gs; rewrite tg in gs.
move/ra:(typ) => typF.
split; move => [ha hb]; move/rb: (ha) =>law2; split => //.
  move:(transport_op bg typ ha) => to.
  apply /(GE_prop4 typF law2) => a b c aF bF cF.
  move:(gs _ aF) (gs _ bF) (gs _ cF) => [a' aE av][b' bE bv][c' cE cv].
  rewrite av bv cv.
  move:(GE_prop2_stable typ ha aE bE) => r1.
  move:(GE_prop2_stable typ ha bE cE) => r2.
  rewrite - (to _ _ bE cE) -(to _ _ aE bE).
  rewrite - (to _ _ aE r2) - (to _ _ r1 cE). 
  by move/(GE_prop4 typ ha): hb => H; rewrite H.
apply/(GE_prop4 typ law2) => a b c aE bE cE.
move:(GE_prop2_stable typ law2 aE bE) => r1.
move:(GE_prop2_stable typ law2 bE cE) => r2.
move: (Vf_target fg); rewrite sg tg => H.
move:(H _ aE) (H _ bE) (H _ cE) => aF bF cF.
move /(GE_prop4 typF ha):  hb => H'.
move:(H' _ _ _ aF bF cF); clear H H'.
move:(transport_op bg typ law2) => to.
rewrite - (to _ _ bE cE) - (to _ _  aE r2) - (to _ _ aE bE) - (to _ _ r1 cE).
by apply: gi; apply: (GE_prop2_stable typ law2).
Qed.
  

Definition GU E s:=
  exists2 z, inc z E &
    forall z', inc z' E -> inc (J (J z z') z') s /\  inc (J (J z' z) z') s. 

Definition unit E s e:= forall z, inc z E -> VL s e z = z /\ VL s z e = z.
Definition un E s := select (unit E s) E.

Lemma GE_prop5 E s : GT E s -> GL E s -> GU E s ->
    exists2 z, inc z E & unit E s z.
Proof.
move =>  type law [z ha hb]; exists z => // a aE.
pose w := (GE_prop2 type law).
move:(hb _ aE) => [r1 r2].
by rewrite /unit -(Law_val w r1) -(Law_val w r2).
Qed.

Lemma GE_prop6 E s z z':
   inc z E -> unit E s z ->  inc z' E -> unit E s z' -> z = z'.
Proof.
by move => sa sb sc sd; rewrite - (proj1 (sb _ sc)) (proj2 (sd _ sa)).
Qed.

Lemma GE_prop7 E s : GT E s -> GL E s -> GU E s ->
   inc (un E s) E /\ unit E s  (un E s).
Proof.
move => ha hb hc.
by case:(select_pr (GE_prop5 ha hb hc) (@GE_prop6 E s)).
Qed.

Lemma GE_prop7_rev E s: GT E s ->  GL E s ->
  forall x, inc x E ->  unit E s x -> GU E s.
Proof.
move => typ law x xE ue.
  move: (GE_prop2 typ law) => ll.
exists x => // z zE. move:(ue z zE) => [ha hb]; split.
  rewrite - {2} ha; apply: (Law_in ll xE zE).
rewrite - {2} hb; apply: (Law_in ll zE xE).
Qed.  

Lemma transport_unit E F g s x:
  bijection_prop g E F -> GT E s -> GL E s ->
  (inc x E /\ unit E s x) ->
  (inc (Vf g x) F /\ unit F (transport s g) (Vf g x)).
Proof.
move => Ha Hb Hc.
have tsg:= (transport_op Ha Hb Hc).
move:(Ha) => [[[fg gi] [_ gs]] sg tg].
rewrite sg in gi gs; rewrite tg in gs.
move => [xE ux]; have yF: inc (Vf g x) F by Wtac.
split => // z zF.
move:(gs _ zF) => [z' zE ->].
by rewrite -(tsg _ _ xE zE)-(tsg _ _ zE xE); move: (ux _ zE) => [-> ->].
Qed.

Lemma transport_un E F g s:
  bijection_prop g E F -> GT E s -> GL E s -> GU E s ->
  un F (transport s g) = Vf g (un E s).
Proof.
move => bg ha hb hd.
move: (GE_prop7 ha hb hd) => up.
move:(transport_unit bg  ha hb up) => [sa sb].
symmetry; apply: select_uniq => // a b aF ua bF ub .
apply: (GE_prop6 aF ua bF ub).
Qed.

  
Lemma transportable_unit:
  transportable (fun E s => (GL E s /\ GA E s) /\ GU E s).
Proof.
move => E F s g bg typ.
move: (proj1 (transportable_GT bg typ) typ) => typF.
have rc:=  (transportable_GA bg typ).
move:(bg) => [[[fg gi] [_ gs]] sg tg].
rewrite sg in gi gs; rewrite tg in gs.
split; move => [ha hb]; move/rc:(ha) => ha'; split => //.
  move:(GE_prop7 typ (proj1 ha) hb) => ra.
  move: (transport_unit  bg typ (proj1 ha)  ra) => [rb1 rb2].
  exact:(GE_prop7_rev typF (proj1 ha') rb1 rb2).
have ll := proj1 ha'.
move:(GE_prop7 typF (proj1 ha) hb); set u := un _ _; move => [uF uu].
move:(gs _ uF) => [v vE vv].
have tsg:= (transport_op bg typ ll).
apply:(GE_prop7_rev typ ll vE) => z zE.
have zF: inc (Vf g z) F by Wtac.
move: (uu _ zF); rewrite vv - !tsg //.
by move => [ea eb]; split; apply: gi => //; apply: (GE_prop2_stable typ ll).  
Qed.


  
Definition GI E s  := forall z z', inc z E -> inc z' E ->
   (exists2 z'', inc z'' E & inc (J (J z z'') z') s)
   /\ (exists2 z''', inc z''' E & inc (J (J z''' z) z') s).

Definition left_inverse E s (x x': Set) := inc x' E /\ VL s x' x = un E s.
Definition right_inverse E s (x x': Set) := inc x' E /\ VL s x x' = un E s.
Definition inverse E s x := select (fun x'  => VL s x' x = un E s) E.


Lemma GE_prop8l E s: GT E s -> GL E s -> GU E s -> GI E s ->
  forall x, inc x E -> exists a, left_inverse E s x a.
Proof.
move => type law inv R4 x xE.
move: (proj1(GE_prop7 type law inv)) => unp.
move: (R4 _ _ xE unp) => [_ [z ha hb]]; exists z => //.
by move: (Law_val  (GE_prop2 type law) hb). 
Qed.


Lemma GE_prop9 E s : GT E s -> GL E s -> GU E s -> GA E s -> GI E s ->
  forall x a b, inc x E ->
  left_inverse E s x a -> right_inverse E s x b -> a = b.  
Proof.
move => pa pb pc ax pd.
move:  (GE_prop7 pa pb pc)=>[uE up] x a b xE [aE ai] [bE bi].
move/(GE_prop4 pa pb): ax => ac.
by move: (ac _ _ _ aE xE bE); rewrite ai bi (proj2 (up _ aE)) (proj1 (up _ bE)).
Qed.

Lemma GE_prop10l E s: GT E s -> GL E s -> GU E s -> GA E s -> GI E s ->
   forall  x a b, inc x E ->
  left_inverse E s x a -> left_inverse E s x b -> a = b.  
Proof.
move => pa pb pc pd pe x a b xE ha hb.
move:(pe _ _ xE (proj1 (GE_prop7 pa pb pc))) => [[c ha' hb'] _]. 
have ci: right_inverse E s x c.
  by split => //;move: (Law_val  (GE_prop2 pa pb) hb'). 
rewrite (GE_prop9 pa pb pc pd pe xE ha ci).
by rewrite -(GE_prop9 pa pb pc pd pe xE hb ci).
Qed.

Lemma GE_prop11l E s: GT E s -> GL E s -> GU E s ->  GA E s -> GI E s ->
  forall x, inc x E ->  left_inverse E s x (inverse E s x).
Proof.
move => pa pb pc pe pd x xE.
set p := (fun x'  => (VL s) x' x = un E s ).
have ha: exists2 x', inc x' E & p x'. 
move:(GE_prop8l pa pb pc pd xE)=> [a [a1 a2]]; ex_tac.
have hb: singl_val2 (inc^~ E) p.
  move => a b aE pra bE prb.
  exact:(GE_prop10l pa pb pc  pe pd xE (conj aE pra) (conj bE prb)).
by move:(select_pr ha hb)=> [hc hd].
Qed.


Lemma GE_prop11r E s: GT E s -> GL E s -> GU E s ->  GA E s -> GI E s ->
  forall x, inc x E -> right_inverse E s x (inverse E s x).
Proof.
move => pa pb pc pd pe x xE.
move: (GE_prop11l pa pb pc pd pe xE) => ha.
move: (pe _ _  xE (proj1 (GE_prop7 pa pb pc))) => [[c ha' hb'] _]. 
have ci: right_inverse E s x c.
  by split => //;move: (Law_val  (GE_prop2 pa pb)  hb'). 
by move:(GE_prop9 pa pb pc pd pe xE  ha ci) => ->.
Qed.

Lemma GE_prop12l E s: GT E s -> GL E s -> GU E s ->  GA E s -> GI E s ->
  forall x y, inc x E ->  inc y E ->  VL s  x (VL s (inverse E s x) y) = y.
Proof.
move => pa pb pc pd pe x y xE yE.
move: (GE_prop11r pa pb pc pd pe xE) => [ha hb].
move /(GE_prop4 pa pb): pd => asx.
by rewrite (asx _ _ _ xE ha yE) hb (proj1(proj2 (GE_prop7 pa pb pc) _ yE)).
Qed.


Lemma GE_prop13a E s: GT E s -> GL E s -> GU E s ->  GA E s -> 
  (forall x, inc x E ->
     exists y, left_inverse E s x y /\ right_inverse E s x y) ->
  GI E s.
Proof.
move => ha hb hc hd hx a b aE bE. 
move: (hx _ aE) => [c [[cE cp] [_ dp]]].
have ll:= (GE_prop2 ha hb).
have  st := (GE_prop2_stable ha hb).
move/ (GE_prop4 ha hb): hd => asc.
move: (GE_prop7 ha hb hc) => [uE up].
move:  (up b bE) => [ul ur].
move: (asc _ _ _ aE cE bE); rewrite dp ul => bv.
move:(asc _ _ _ bE cE aE); rewrite cp  ur => bv2.
move: (st _ _ cE bE)  (st _ _ bE cE) =>  dce  bde.
split.
  by exists(VL s c b)  => //; rewrite - {2} bv; apply:(Law_in ll). 
by  exists(VL s b c)  => //; rewrite  {2} bv2; apply:(Law_in ll). 
Qed.

Lemma transport_inv E F g s x y:
  bijection_prop g E F -> GT E s ->  GL E s -> GU E s ->
  inc x E -> left_inverse E s x y ->
  left_inverse F (transport s g) (Vf g x) (Vf g y).
Proof.
move => bg ha hb hc xE [yE xy].
move:(bg) => [[[fg gi] [_ gs]] sg tg].
rewrite sg in gi gs; rewrite tg in gs.
have xF: inc (Vf g x) F by Wtac.
have yF: inc (Vf g y) F by Wtac.
split => //; rewrite(transport_un bg ha hb hc).
by rewrite - (transport_op bg ha hb yE xE) xy.
Qed.

Lemma transport_inverse E F g s x:
  bijection_prop g E F -> GT E s ->  GL E s -> GA E s ->  GU E s ->  GI E s ->
  inc x E -> Vf g (inverse E s x) = inverse F (transport s g) (Vf g x).
Proof.
move => bg ha hb hc hd he xE.
move:(bg) => [[[fg gi] [_ gs]] sg tg].
rewrite sg in gi gs; rewrite tg in gs.
move: (GE_prop11l ha hb hd hc he xE); set ix := inverse _ _ _.
move => [pa pb].
have ixf: inc (Vf g ix) F by Wtac.   
have t1:= (transport_un bg ha hb hd).
have ra: VL (transport s g) (Vf g ix) (Vf g x) = un F (transport s g).
  by rewrite t1 -(transport_op  bg  ha hb pa xE) pb.
apply: select_uniq => //  a b /= aF ap bF bp.
move:(gs _ aF) (gs _ bF) => [u uE uv] [v vE vv].
have  st := (GE_prop2_stable ha hb).
move: (proj1 (GE_prop7 ha hb hd)) => iuE.
move: ap bp.
rewrite uv vv t1 -(transport_op  bg  ha hb uE xE) => eq1.
move:(gi _ _ (st _ _ uE xE) iuE eq1) => iv1.
rewrite -(transport_op  bg  ha hb vE xE)  => eq2.
move:(gi _ _ (st _ _ vE xE) iuE eq2) => iv2.
by congr (Vf g); apply: (GE_prop10l ha hb hd hc he xE).
Qed.


Lemma transportable_GI:
  transportable (fun E s => ((GL E s /\ GA E s) /\ GU E s) /\ GI E s).
Proof.
move => E F s g bg typ.
move: (proj1 (transportable_GT bg typ) typ) => typF.
have rc:=  (transportable_unit bg typ).
move:(bg) => [[[fg gi] [_ gs]] sg tg].
rewrite sg in gi gs; rewrite tg in gs.
split; move => [ha hb]; move/rc:(ha) => ha'; split => //.
   move: ha ha' =>  [[lE aE]  uE] [[lF aF]  uF].
   apply:(GE_prop13a typF lF uF aF) => x xF.
   move:(gs _ xF) => [y yE yv].
   move:(GE_prop11l typ lE uE aE hb yE) => ll.
   move:(transport_inv bg typ lE uE yE ll) => hu.
   move:(GE_prop11r typ lE uE aE hb yE) => lr.
   have lr1: left_inverse E s (inverse E s y) y by case: lr.
   move:(transport_inv bg typ lE uE (proj1 ll) lr1) => hv1.
   have hv: right_inverse F (transport s g) (Vf g y) (Vf g (inverse E s y)) .
     move: hv1 => [rx ry]; split => //; exact: (proj1 hu).
   rewrite yv.
   by exists (Vf g (inverse E s y)).
move: ha' ha =>  [[lE aE]  uE] [[lF aF]  uF].
apply:(GE_prop13a typ lE uE aE) => x xE.
have xF: inc (Vf g x) F by Wtac.
move : (GE_prop11l typF lF uF aF hb xF) (GE_prop11r typF lF uF aF hb xF).
rewrite/left_inverse/right_inverse (transport_un bg typ lE uE).
set y := inverse F _ _; move => [yF].
move:(gs _ yF)=> [z zE ->].
have  st := (GE_prop2_stable typ lE). 
move:(st _ _ zE xE) (st _ _ xE zE) => h1f h2f.
rewrite - (transport_op  bg  typ lE  zE xE).
rewrite - (transport_op  bg  typ lE  xE zE) => e1 [_ e2].
have unE:= proj1(GE_prop7 typ lE uE).
by exists z; split => //; split => //; apply: gi.
Qed.

  
End GroupExample.

End StructureExample.


From mathcomp Require Import seq.

Module Structure.



Inductive Tree :=
  | Tbase: nat -> Tree 
  | Tpowerset : Tree -> Tree
  | Tproduct : Tree -> Tree -> Tree.

Fixpoint Tdepth e:=
  match e with
    | Tbase _ => 0
    | Tpowerset e' => (Tdepth e').+1
    | Tproduct e' e'' => (maxn (Tdepth e') (Tdepth e'')).+1
end.

Fixpoint Tsize e:=
  match e with
    | Tbase n => n
    | Tpowerset e' => Tsize e'
    | Tproduct e' e'' => maxn (Tsize e') (Tsize e'')
  end.

  
Section Tree.

Definition Tb x := J \0c x.
Definition Tp x := J \1c x.
Definition Tx x y := J \2c (J x y).
  
Definition tset_base := fun_image Nat Tb.

Definition tset_next E :=
  fun_image E Tp
  \cup fun_image (E \times E) (fun p => J \2c p)
  \cup E. 

Lemma tset_baseP x: inc x tset_base <-> exists2 n, natp n & x = Tb n.
Proof. exact:funI_P. Qed.

Lemma tset_basei n: natp n -> inc (Tb n) tset_base.
Proof. by move => nN; apply/(tset_baseP); exists n. Qed.

Lemma tset_nextP E x:  inc x (tset_next E) <-> 
  [\/ exists2 y, inc y E  & x = Tp y,
      exists y z, [/\ inc y E, inc z E & x = Tx y z]
    | inc x E].
Proof.
split.
  case/setU2_P; last by move => xe; constructor 3.
  case /setU2_P; first by move/funI_P => h; constructor 1.
  move /funI_P => [y /setX_P [ya yb yc] ->]; constructor 2.
  by exists (P y), (Q y); rewrite /Tx ya.
case => h.
- by apply /setU2_P;left; apply /setU2_P;left; apply/funI_P.
- apply /setU2_P;left; apply /setU2_P;right; apply/funI_P.
  by move: h => [y [z [yE zE ->]]]; exists (J y z) => //; apply: setXp_i.
- by apply /setU2_P;right.
Qed.

Definition tset_index := induction_term (fun _ x => tset_next x) tset_base.
Definition tset := unionf Nat tset_index.
Definition treep x := inc x tset.

Lemma tset_index0:  tset_index \0c = tset_base.
Proof. by apply:induction_term0. Qed.

Lemma tset_indexS n:  natp n -> 
    tset_index (csucc n) = tset_next (tset_index n).
Proof. exact: induction_terms. Qed.

Lemma tsetP x: treep x <-> exists2 n, natp n & inc x (tset_index n).
Proof. exact:setUf_P. Qed.

Lemma tset_base_hi x: inc x tset_base -> treep x.
Proof.
by move => xb; apply/tsetP; exists \0c;[ exact NS0 |rewrite tset_index0 ].
Qed.

Lemma tset_min x: treep x ->
  inc x tset_base \/
  exists n, [/\ natp n, inc x (tset_index (csucc n)) & ~inc x (tset_index n)].
Proof.
move/tsetP => [n nN ha].
case: (least_int_prop2 nN ha (p := fun t => inc x (tset_index t))).
   by rewrite tset_index0; left.
by set m := cpred _=> j; right; exists m.
Qed.


Definition tdepth x := intersection (Zo Nat (fun n => inc x (tset_index n))).

Lemma tdepth1 x (n:= tdepth x): treep x -> 
   [/\ natp n, inc x (tset_index n) &
    forall m, natp m -> inc x (tset_index m) -> n <=c m].
Proof.
move => sa; rewrite /n/tdepth; set U := Zo _ _.
have csu: cardinal_set U by move => t /Zo_P [/CS_nat ].
move/tsetP: (sa) => [k ka kb].
have neu: nonempty U by exists k;apply/Zo_P.
move: (cle_wor' csu neu); rewrite -/(tdepth x); move => [/Zo_P[sc sd] se].
by split => // m ma mb; apply:se; apply: (Zo_i ma mb).
Qed.

Lemma NS_tdepth x: treep x -> natp (tdepth x).
Proof. by case /tdepth1. Qed.
 
Lemma tdepth2 x m: treep x -> natp m -> (tdepth x) <=c m ->
  inc x (tset_index m).
Proof.
move => /tdepth1 [sa sb _] mn le1.
rewrite -(cdiff_pr le1).
move:(NS_diff (tdepth x) mn); move: (m -c tdepth x); apply: Nat_induction.
  by rewrite (csum0r (proj31 le1)).
move => n nN xa.
rewrite (csum_via_succ _ (CS_nat nN)) (tset_indexS (NS_sum sa nN)).
by apply/tset_nextP; constructor 3.
Qed.

Lemma tdepth3 x m: natp m -> inc x (tset_index m) -> (tdepth x) <=c m.
Proof.
move => sa sb.
have ts: treep x by apply/tsetP; exists m.
by move: (tdepth1 ts) => [sc sd se]; exact: (se _ sa sb).
Qed.


Lemma tdepth4 x: treep x -> tdepth x = \0c -> inc x tset_base.
Proof.
by move => /tdepth1 [_ sa _] sb; move: sa; rewrite sb tset_index0.
Qed.

Lemma tdepth_prop x n: treep x -> natp n -> tdepth x = (csucc n) ->
  (exists y, [/\ treep y, tdepth y <=c n & x = Tp y]) \/
  (exists y z, [/\ treep y, treep z, tdepth y <=c n, tdepth z <=c n &
     x = Tx y z]).
Proof.
move => xt nN dx.
move: (proj32 (tdepth1 xt)); rewrite dx (tset_indexS nN); case/tset_nextP.
- move => [y ya yb]; constructor 1; exists y; split => //.
  by apply /tsetP; exists n.
  by apply:tdepth3.
- move => [y [z [ya za ->]]]; constructor 2; exists y,z; split => //.
  by apply /tsetP; exists n.
  by apply /tsetP; exists n.
  by apply:tdepth3.
  by apply:tdepth3.    
- by move => h; move:(tdepth3 nN h); rewrite dx => h';case:(cltNge (cltS nN)). 
Qed.

Lemma tdepth_prop_inv:
  [/\ forall n, natp n -> treep (Tb n)  /\ tdepth (Tb n) = \0c,
  forall t, treep t -> treep (Tp t) /\ tdepth (Tp t) = csucc (tdepth t) &
  forall t t', treep t -> treep t' -> treep (Tx t t') /\
           tdepth (Tx t t') = csucc (cmax (tdepth t) (tdepth t'))  ].
Proof.
split.
- move =>n nN.
  have xb0: inc (Tb n) (tset_index \0c).
    by rewrite tset_index0; apply:tset_basei.
  move: (tdepth3 NS0 xb0) => /cle0 tz.
  split => //; apply/tsetP; exists \0c => //; exact: NS0.
- move => t tS; move: (tdepth1 tS) => [sa sb sc].
  have sd := (NS_succ sa).
  have tsn: inc (Tp t) (tset_index (csucc (tdepth t))).
    by rewrite (tset_indexS sa); apply/tset_nextP; constructor 1; exists t.
  have nts: treep (Tp t)  by apply/tsetP; exists (csucc (tdepth t)).
  split => //; move: (tdepth3 sd tsn) => le1.
  case:  (equal_or_not (tdepth (Tp t)) \0c) => tnz.
    by move:(tdepth4 nts tnz) => /tset_baseP [n nN /pr1_def e01]; case:card1_nz.
  move: (cpred_pr  (NS_le_nat le1  sd) tnz) => [ma mb].
  case: (tdepth_prop nts ma mb).
     move => [y [ya yb /pr2_def yc]]; apply: cleA => //.
     by rewrite mb {1} yc; apply: cleSS.
  by move => [y [z [_ _ _ _ /pr1_def eq12]]]; case: card_12.
- move => t t' tS tS'; move: (tdepth1 tS)(tdepth1 tS')=> [sa sb sc][ra rb rc].
  case: (Nmax_p1 sa ra).
  set m :=  (cmax (tdepth t) (tdepth t')) => mN max1 max2.
  have smN:= (NS_succ mN).
  have tsn: inc (Tx t t') (tset_index (csucc m)).
    rewrite (tset_indexS mN); apply/tset_nextP; constructor 2; exists t, t'.
    by split=>//; [apply: (tdepth2 tS mN max1) | apply: (tdepth2 tS' mN max2) ].
  have nts: treep (Tx t t') by apply/tsetP; exists (csucc m).
  split => //.
  move: (tdepth3 smN tsn) => le1.
  case:(equal_or_not (tdepth (Tx t t')) \0c) => tnz.
    by move:(tdepth4 nts tnz)=> /tset_baseP [n nN /pr1_def e02]; case: card2_nz.
  move: (cpred_pr (NS_le_nat le1 smN) tnz) => [ma mb].
  case: (tdepth_prop nts ma mb).
    by move => [y [_ _ /pr1_def eq12]]; case: card_12.
  move => [y [z [ yT zT dy dz /pr2_def eq1]]]; apply:cleA => //.
  rewrite mb; apply:cleSS.
  by move: (cmax_p0 dy dz); rewrite -(pr1_def eq1) - (pr2_def eq1) -/m mb.
Qed.

Lemma TS_base n: natp n ->treep (Tb n).
Proof. by case/(proj31 tdepth_prop_inv). Qed.

Lemma TS_powerset t: treep t ->  treep (Tp t).
Proof. by case/(proj32 tdepth_prop_inv). Qed.

Lemma TS_product t t': treep t -> treep t' ->  treep (Tx t t').
Proof. by move => ha hb;case:(proj33 tdepth_prop_inv _ _ ha hb). Qed.

Lemma tree_ind (p: property):
  (forall n, natp n -> p (Tb n)) ->
  (forall x, treep x -> p x -> p (Tp x)) ->
  (forall x x', treep x -> treep x' -> p x -> p x' -> p(Tx x x')) ->
  (forall x, treep x -> p x).
Proof.
move => ha hb hc x xt; move: (NS_tdepth xt) => ns.
move: (cleR (CS_nat ns)); move: ns.
move: {1 3}(tdepth x) => m mn; move: m mn x xt; apply: Nat_induction.
  move => x xt /cle0 => dz. 
  by move: (tdepth4 xt dz) => /tset_baseP [n nN ->]; apply: ha.
move => n nN Hrec x xt /cle_eqVlt []; last by move/(cltSleP nN); apply: Hrec.
case/(tdepth_prop xt nN).
  by move=>[y [ys dy ->]]; apply: hb => //; apply: Hrec.
move => [y [z [ya za hy hz ->]]].
by apply: hc => //; apply: Hrec.
Qed.



Section StratifiedTheory.

Variable h1: Set -> Set.
Variable h2: Set -> Set.
Variable h3: Set -> Set -> Set.

Lemma tree_rec_def_aux1: forall x, treep x -> ordinalp (tdepth x).
Proof. by move => x /NS_tdepth /OS_nat. Qed.

Definition tree_stratified i E := 
  forall x, inc x E <-> treep x /\ tdepth x <o i.

Lemma tree_rec_def_aux2a: tree_stratified \0c emptyset.
Proof. by split;[ move/in_set0 | move => [ha /olt0] ]. Qed.

Lemma tree_rec_def_aux2b i: omega0 <=o i -> tree_stratified i tset.
Proof.
move => h x; split; [move => xt; split => // |  by case].
move: (NS_tdepth xt) => /(oltP OS_omega) ha.
exact: (olt_leT ha h).
Qed.

Lemma tree_rec_def_aux2c i: i <o omega0 -> i <> \0c -> 
   tree_stratified i (tset_index (cpred i)).
Proof.
move => ii inz.
move/(oltP OS_omega): ii => iN.
move: (cpred_pr iN inz) => [ha hb].
move => x; split => xE.
  split; first by apply/tsetP; exists (cpred i).
  by apply: oclt; rewrite hb; apply /(cltSleP ha); apply:tdepth3.
move: xE =>[ xE dx].
apply:(tdepth2 xE ha);  apply /(cltSleP ha); rewrite - hb.
by apply: (oclt3 (CS_nat (NS_tdepth xE)) (CS_nat iN)). 
Qed.

Lemma tree_rec_def_aux2: forall i, ordinalp i -> exists E, tree_stratified i E.
Proof.
move => i oi; case:(oleT_el OS_omega oi) => ii.
  by exists tset; apply:tree_rec_def_aux2b.
case: (equal_or_not i \0c) => inz.
   exists emptyset; by rewrite inz;apply:tree_rec_def_aux2a.
by exists  (tset_index (cpred i)); apply: tree_rec_def_aux2c.
Qed.

Definition tstratified i := 
  Yo (i = \0c) emptyset
     (Yo (omega0 <=o i) tset (tset_index (cpred i))).

Lemma tstratified_val i: ordinalp i ->
  stratified_set treep tdepth i = tstratified i.
Proof.
move => oi.
have H:= (stratified_setP tree_rec_def_aux2 oi); rewrite /tstratified.
case: (equal_or_not i \0c) => iz; Ytac0.
  apply/set0_P => x; case/(stratified_setP tree_rec_def_aux2 oi) => _.
  by rewrite iz;move /olt0.
case:(oleT_el OS_omega oi) => ii.
  Ytac0; move:(tree_rec_def_aux2b ii)=> ww.
  set_extens t; first  by move/(stratified_setP tree_rec_def_aux2 oi) => /ww.
  by move/ww/(stratified_setP tree_rec_def_aux2 oi).
rewrite (Y_false (oltNge ii)); move:(tree_rec_def_aux2c ii iz)=> ww.
set_extens t; first  by move/(stratified_setP tree_rec_def_aux2 oi) => /ww.
by move/ww/(stratified_setP tree_rec_def_aux2 oi).
Qed. 

Definition tree_rec_prop x f := 
  Yo (P x = \0c) (h1 (Q x))
     (Yo (P x = \1c) (h2 (Vg f (Q x))) (h3 (Vg f (P (Q x))) (Vg f (Q (Q x))))).

Definition tree_rec := stratified_fct treep tree_rec_prop tdepth.

Lemma tree_recdef_p x: treep x ->  tree_rec x = 
   tree_rec_prop x (Lg (tstratified (tdepth x)) tree_rec).
Proof.
move: (stratified_fct_pr tree_rec_prop tree_rec_def_aux1 tree_rec_def_aux2).
rewrite -/tree_rec => h xt.
move/OS_nat:(NS_tdepth xt) => oi.
by rewrite (h _ xt) (tstratified_val oi).
Qed.

Lemma tree_recdef_pb' n: natp n -> tree_rec (Tb n) = h1 n.
Proof.
move => h. 
have xt:= TS_base h.
by rewrite (tree_recdef_p xt) /tree_rec_prop pr1_pair pr2_pair; Ytac0.
Qed.
  
Lemma tree_recdef_pb x: inc x tset_base -> tree_rec x = h1 (Q x).
Proof.
move => ha.
have xt:= (tset_base_hi ha).
by move/tset_baseP: ha => [n nN ->]; rewrite (tree_recdef_pb' nN) /Tb; aw.
Qed.


Lemma tree_recdef_pp x: treep x -> tree_rec (Tp x)  = h2 (tree_rec x).
Proof.
move: card1_nz => n01 ha.
move: (proj32 (tdepth_prop_inv) _ ha) => [hb hc].
move: (NS_tdepth ha) => iN.
rewrite (tree_recdef_p hb) /tree_rec_prop /Tp; aw; Ytac0; Ytac0; rewrite LgV//.
rewrite /tstratified hc (Y_false (@succ_nz _)) (cpred_pr2 iN); Ytac w => //. 
exact:(proj32 (tdepth1 ha)).
Qed.

Lemma tree_recdef_px x y: treep x -> treep y ->
   tree_rec (Tx x y)  = h3 (tree_rec x) (tree_rec y).
Proof.
move: card1_nz => n01 ha ha'.
move: card_12 card2_nz => c12 c02.
move: (proj33 (tdepth_prop_inv) _ _ ha ha') => [hb hc].
move: (NS_tdepth ha) (NS_tdepth ha') => iN iN'.
case: (Nmax_p1 iN iN').
set m :=  (cmax (tdepth x) (tdepth y)) => mN max1 max2.
have ra: inc x (tstratified (tdepth (Tx x y))).
  rewrite /tstratified hc  (Y_false (@succ_nz _)); Ytac w => //.
  by move: (tdepth2 ha mN max1); rewrite (cpred_pr2 mN).
have rb: inc y (tstratified (tdepth (Tx  x y))).
  rewrite /tstratified hc  (Y_false (@succ_nz _)); Ytac w => //.
  by move: (tdepth2 ha' mN max2); rewrite (cpred_pr2 mN).
rewrite (tree_recdef_p hb) /tree_rec_prop /Tx; aw; Ytac0; Ytac0; rewrite !LgV//.
Qed.


Lemma tree_recdef_stable E:
  (forall n, natp n -> inc (h1 n) E) ->
  (forall x, inc x E -> inc (h2 x) E) ->
  (forall x x', inc x E -> inc x' E -> inc (h3 x x') E) ->
  (forall x, treep x -> inc (tree_rec x) E).
Proof.
move => ha hb hc.
apply: tree_ind.
- by move => n nN; rewrite tree_recdef_pb' //; apply: ha.
- by move => x xt; rewrite tree_recdef_pp //; apply: hb.
- move => x y xt yt; rewrite tree_recdef_px //; apply: hc.
Qed.


End StratifiedTheory.



Definition tree_depth_alt :=
  tree_rec (fun _ => \0c) csucc (fun a b => csucc (cmax a b)).

Lemma tree_depth_altE  x: treep x  -> (tree_depth_alt x) = tdepth x.
Proof.
move: x;  rewrite /tree_depth_alt;apply: tree_ind.
- move => n nN;move: (proj31 (tdepth_prop_inv) _ nN) => [_ ->].
  by rewrite tree_recdef_pb //; apply:tset_basei.
- move => x xt h; move: (proj32 (tdepth_prop_inv) _ xt) => [sa sb].
  by rewrite sb tree_recdef_pp // h. 
- move => x y xt yt h1 h2; rewrite  tree_recdef_px // h1 h2.
  by move: (proj33 (tdepth_prop_inv) _ _ xt yt) => [_ ->].
Qed.

Fixpoint Tpositive e:=
  match e with
    | Tbase n =>  n != 0
    | Tpowerset e' =>  Tpositive e'
    | Tproduct e' e'' => (Tpositive e') && (Tpositive e'')
  end.


Lemma tree_rec_bool h1 (f := tree_rec h1 id (fun a b => (cmin a b))):
   (forall x, natp x -> h1 x <=c \1c) -> (forall x, treep x -> f x <=c \1c). 
Proof.
have Hb v: inc v \2c <-> v <=c \1c.
  apply: (iff_trans (iff_sym (NltP NS2 v))).
  rewrite - succ_one; exact:(cltSleP NS1).
move => Ha x xT; apply/Hb; apply:tree_recdef_stable => //.
  by move => n nn; apply/Hb; apply: Ha.
by  move => u v u1 u2; rewrite /cmin/Gmin; Ytac w.
Qed.


Definition tree_to_pos :=
  tree_rec (fun  n => Yo (n = \0c) \0c \1c) id (fun a b => (cmin a b)).

Lemma tree_to_pos_p1:
  [/\ (forall x, natp x -> tree_to_pos (Tb (csucc x)) = \1c),
   (tree_to_pos (Tb \0c) = \0c),
   (forall x, treep x -> tree_to_pos (Tp x) = tree_to_pos x) &
   (forall x x', treep x -> treep x' ->
      tree_to_pos (Tx x x') = cmin (tree_to_pos x) (tree_to_pos x'))].
Proof.
rewrite /tree_to_pos; split.
- move => x xN.
  have ha:= (tset_basei (NS_succ xN)).
  by rewrite tree_recdef_pb // pr2_pair Y_false //; exact: succ_nz.
- by rewrite (tree_recdef_pb _ _ _ (tset_basei NS0)) pr2_pair Y_true.
- by move => x xT; rewrite tree_recdef_pp.
- by move => x y xT yT;rewrite tree_recdef_px.
Qed.


Definition tree_is_pos x := tree_to_pos x = \1c.

Lemma tree_to_pos_p2:
  [/\ (forall x, natp x -> (tree_is_pos (Tb x) <-> x <> \0c)),
   (forall x, treep x -> (tree_is_pos (Tp x) <-> tree_is_pos x)) &
   (forall x x', treep x -> treep x' ->
      (tree_is_pos (Tx x x') <-> ((tree_is_pos x) /\ (tree_is_pos x'))))].
Proof.
rewrite /tree_is_pos;split.
- move => n nN; case: (equal_or_not n \0c) => nz.
    rewrite nz; move:(tree_to_pos_p1) => [_ -> _ _]; split => // w.
    by case:card1_nz.
  have [sa sb]:= (cpred_pr nN nz); rewrite sb.
  move:(tree_to_pos_p1) => [sc _ _ _]; rewrite (sc _ sa); split => //.
  by move => _; apply: succ_nz.
- by move => x xT; move:(tree_to_pos_p1) => [_ _ sc _]; rewrite (sc _ xT). 
- move => x x' xT xT'.
  move: (tree_to_pos_p1) => [_ _ _ sd]; rewrite (sd _ _ xT xT').
  split; last by  move => [-> ->]; rewrite /cmin/Gmin; Ytac w.
  have ha: forall x, natp x -> (fun  n => Yo (n = \0c) \0c \1c) x <=c \1c.
    move => n nN /=; Ytac w; [ exact: cle_01 | exact (cleR CS1)].
  move: (tree_rec_bool ha xT) (tree_rec_bool ha xT'). 
  rewrite -/tree_to_pos /cmin/Gmin; move => ra rb.
  Ytac w => vv; split => //;apply: cleA => //; rewrite - vv //.
  by move:w;rewrite vv; case.
Qed.

Definition tree_size := tree_rec id id cmax.

Lemma tree_size_p:
  [/\ (forall x, natp x -> tree_size (Tb x) = x),
   (forall x, treep x -> tree_size (Tp x) = tree_size x) &
   (forall x y, treep x ->treep y  -> 
   tree_size (Tx x y) = cmax (tree_size x) (tree_size y)) ].
Proof.
rewrite /tree_size;split.
- by move => n nN; rewrite tree_recdef_pb'.
- by move => x xt; rewrite tree_recdef_pp.
- by move => x y xt yt; rewrite tree_recdef_px.
Qed.

Lemma NS_tree_size x: treep x -> natp (tree_size x).
Proof.
by apply:tree_recdef_stable => // a b aN bN; apply:Gmax_E.
Qed.

Fixpoint Tree_to_tree e:=
  match e with
    | Tbase n =>  J \0c (nat_to_B n)
    | Tpowerset e' => J \1c (Tree_to_tree e')
    | Tproduct e' e'' => J \2c (J (Tree_to_tree e') (Tree_to_tree e''))
end.

Lemma Tree_to_tree_prop e (t := Tree_to_tree e):
  [/\ treep t,
      tdepth t = nat_to_B (Tdepth e),
      tree_size t = nat_to_B (Tsize e)&
      tree_is_pos t <-> Tpositive e].
Proof.
rewrite /t {t};elim:e.
- move => n /=; move: (nat_to_B_Nat n) => sa;move:(proj31 tdepth_prop_inv _ sa).
  move => [sc sd];rewrite(proj31 tree_size_p _ sa).
  move:(proj31 tree_to_pos_p2 _ sa) => h.
  split => //; apply: (iff_trans h); case: (n); first by split.
  move => m; split => //= _; exact: succ_nz.
- move => e [ha hb hc hd] /=.
  rewrite (proj32 tree_size_p _ ha).
  have he:=(iff_trans (proj32 tree_to_pos_p2 _ ha) hd).
  move:(proj32 tdepth_prop_inv _ ha) => [hf ->]; rewrite hb; split => //.
- move => e [ha hb hc hd] e' [ha' hb' hc' hd'] /=.
  rewrite (proj33 tree_size_p _ _ ha ha').
  move:(proj33 tdepth_prop_inv _ _ ha ha') => [he ->].
  have hf:= (proj33 tree_to_pos_p2 _ _ ha ha').
  rewrite hb hb' hc hc' !(nat_to_B_max); split => //.
  split; first by move/hf => [/hd -> /hd' ->].
  by move/andP => [/hd hd1 /hd' hd2]; apply/hf.
Qed.


Lemma Tree_to_tree_injective: injective Tree_to_tree.
Proof.
elim.
+  move => n [ m | e | e e'] /= => eq.
  - by move: (pr2_def eq) => eq'; rewrite (nat_to_B_injective eq').
  - by case: card1_nz; move: (pr1_def eq). 
  - by case: card2_nz; move: (pr1_def eq). 
+  move => e0 Hr [ m | e | e e'] /= => eq.
  - by case: card1_nz; move: (pr1_def eq).
  - by move: (pr2_def eq) => /Hr ->.
  - by case: (card_12); move: (pr1_def eq). 
+  move => e0 Hr e1 Hr' [ m | e | e e'] /= => eq.
  - by case: card2_nz; move: (pr1_def eq).
  - by case: (card_12); move: (pr1_def eq). 
    move: (pr2_def eq) => eq'.
    move: (pr1_def eq') => /Hr ->.
    by move: (pr2_def eq') => /Hr' ->.
Qed.

Lemma Tree_to_tree_surjective x: treep x -> exists e, x = Tree_to_tree e.
Proof.
move:x;apply: tree_ind.
- move => n nN; move:(nat_to_B_surjective nN) => [k ->].
  by exists (Tbase k).
- by move => x _ [e ->]; exists (Tpowerset e).
by move => x x' _ _ [e ->] [e' ->]; exists (Tproduct e e'). 
Qed.
  
End Tree.


(** Inverse Limits and Direct Limits *)







(* Echelons *)


Definition ech_good x i :=  \1c <=c x /\ x <=c i.

Definition echelon c :=
  slist_E c (Nat \times Nat) /\
  forall i, i <c (slength c) ->
            let a:= P (Vg c i) in
            let b:= Q (Vg c i) in
            (b = \0c -> ech_good a i) /\
            (b <> \0c -> a <> \0c -> ech_good a i /\ ech_good b i).


Definition esize c :=
  \csup(range (Lg (domain c) (fun i=> Yo (P (Vg c i) = \0c) (Q (Vg c i)) \0c))).


Lemma echelon_p1 c: echelon c ->
  \0c <c slength c ->
  exists b, [/\ natp b, \0c <c b & Vl c \1c = J \0c b].
Proof.
move => [pa pb] pc.
have nN:= (proj2 (proj1 pa)). 
move/cge1P: pc => ha.
move /setX_P:  (Vl_p1 pa (cleR CS1) ha) => [ra rb rc].
have pd: \0c <c slength c by  apply/(cleSltP NS0); rewrite succ_zero.
move: (pb _ pd); simpl; move /setX_P:  (Vl_p1 pa (cleR CS1) ha). 
rewrite /Vl cpred1; set a:= P _; set b := Q _; move => [sa sb sc] [sd se].
have Ha w: ech_good w \0c -> False.
  by move => [la lb]; move: (cltNge clt_01) (cleT la lb).
case(equal_or_not b \0c) => bz; first by move: (Ha _ (sd  bz)).
case(equal_or_not a \0c) => az; last by case: (Ha _ (proj1 (se bz az))).
have bp:= (card_ne0_pos (CS_nat sc) bz).
by exists b; rewrite - sa -/a az. 
Qed.

Lemma echelon_p1' c: echelon c ->
  \0c <c slength c ->
  exists b, [/\ natp b, \0c <c b & Vg c \0c = J \0c b].
Proof.
move => h1 h2; move: (echelon_p1 h1 h2) => [n [bN bp v]]; exists n; split=> //.
by rewrite  -v /Vl cpred1.
Qed.  

Lemma esize_empty c : echelon c ->
  slength c = \0c -> esize c = \0c.
Proof.
move => [[ec _] _] sz.
rewrite /esize (slist_domain ec) sz Nint_co00 /Lg funI_set0 range_set0.
by rewrite setU_0.
Qed.

Lemma esize_prop1 c (n:= esize c) (m:=slength c):
  echelon c -> \0c <c m ->
  [/\ natp n, \0c <c n, exists2 j, j <c m & Vg c j = J \0c n &
   forall j, j <c m -> P (Vg c j) = \0c -> Q (Vg c j) <=c n].
Proof.
move => ha hb.
move: (echelon_p1 ha hb) => [b0 [b0N b0p cb0]].
have b4: Vg c \0c = J \0c b0 by rewrite - cb0 /Vl cpred1.
rewrite /n/esize {n}; set r := range _ .
move:ha =>[[pa pb] pc].
have mN := (proj2 pa).
have rN: sub r Nat.
  move => v  /Lg_range_P [i idc ->]; Ytac pz; last by apply: NS0.
  by move:(pb _ (inc_V_range (proj1 pa) idc)) => /setX_P [].
have fsr: finite_set r.
  apply: (finite_range); aww.
  by rewrite - (NintE mN); apply: finite_Nint.
have zd: inc \0c (domain c) by apply /(NltP mN).
have b0r: inc b0 r by apply/Lg_range_P;exists \0c => //; rewrite b4; aw; Ytac0.
have nr: nonempty r  by exists b0.
move: (finite_subset_Nat rN fsr nr) => [n nir nmax].
have nN:= (rN _ nir).
have ->: union r = n.
  have csr: cardinal_set r by move => i /rN /CS_nat.
  apply: (cleA (card_ub_sup (CS_nat nN) nmax) (card_sup_ub csr nir)).
have np:=(clt_leT b0p (nmax _ b0r)).
split => //.
  move/Lg_range_P: (nir) => [b1 b1d].
  move:(pb _ (inc_V_range (proj1 pa) b1d)) => /setX_P [qa qb qc].
  Ytac fs => nn; last by move:(proj2 np); rewrite nn.
  by exists b1;[ apply /(slist_domainP pa) | rewrite - qa fs - nn ].
move => j ljm pz; apply:nmax; apply/Lg_range_P; exists j.
  by apply /(slist_domainP pa).
by rewrite pz; Ytac0.
Qed.

Lemma NS_esize c: echelon c ->
  natp (esize c).
Proof.
move => h.
have sN:=(proj2 (proj1 (proj1 h))).
case (equal_or_not (domain c) \0c) => sz.
  rewrite (esize_empty h sz); apply: NS0.
by case:(esize_prop1 h (card_ne0_pos (CS_nat sN) sz)).  
Qed.


Lemma esize_prop2 c n (m:=slength c):
  echelon c -> 
  (exists2 j, j <c m & Vg c j = J \0c n) ->
  (forall j, j <c m -> P (Vg c j) = \0c -> Q (Vg c j) <=c n) ->
  esize c = n.
Proof.
move => ha [j ja jb] hc.
have mp:= (cle_ltT (cle0x (proj31_1 ja)) ja).
move:(esize_prop1 ha mp); set k := esize c.
move => [kN kp [j2 j2a j2b] hd].
apply: cleA.
  have pa:P (Vg c j2) = \0c by rewrite j2b; aw.
  by move: (hc _ j2a pa); rewrite j2b; aw.
have pa:P (Vg c j) = \0c by rewrite jb; aw.
by move: (hd _ ja pa); rewrite jb; aw.
Qed. 

Definition Ech_base n := Lg \1c (fun z => (J \0c n)).

Lemma Ech_base_prop n (c:= Ech_base n):
  natp n -> \0c <c n ->
  [/\ echelon c, Vg c \0c = J \0c n, \0c <c slength c & esize c = n].
Proof.
move => ha hb.
have nz:=(nesym (proj2 hb)).
have i01: inc \0c \1c by apply: set1_1.
have lt01 := clt_01.
have ns1 := NS1.
have vz:  Vg c \0c = J \0c n by rewrite /c/Ech_base;rewrite LgV. 
have r0: slength c = \1c by rewrite /c /Ech_base /slength Lgd.
have hc: echelon c.
  split; last by rewrite r0 => i /clt1 ->; rewrite vz; aw; split.
  rewrite /c/Ech_base; split; first split; aww.
  move => i /Lg_range_P[_ _ ->]; apply: setXp_i => //; apply: NS0.
have sp: \0c <c slength c by rewrite /slength/c /Ech_base Lgd.
split => //.
apply: (esize_prop2 hc).
  by exists \0c => //; rewrite r0.
move => j; rewrite r0 /c/Ech_base => /(NltP NS1)jz; rewrite ! LgV//; aw.
move => _; exact: (cleR (CS_nat ha)).
Qed.

Definition Ech_powerset c:=
  c +s1 J (slength c) (J (slength c) \0c).

Lemma Ech_powerset_prop c (m := slength c)(c':= Ech_powerset c):
  echelon c -> \0c <c m ->
  [/\ echelon c',  slength c' =  csucc m, esize c' =  esize c,
     Vg c' m = J m \0c & forall k, k <c m -> Vg c' k = Vg c k].
Proof.
move => sa sb.
move: (esize_prop1 sa sb) => sc.
move: sa => [[[qa qb] sa2] sa3].
have ra: sub (range c') (Nat \times Nat).
  rewrite range_setU1 => i/setU1_P; case; first by apply: sa2.
  move => ->; apply: setXp_i => //; apply:NS0. 
have rb: ~ inc (slength c) (domain c).
  by apply:ordinal_irreflexive; apply: OS_nat.
have dc1: domain c' = osucc (domain c) by rewrite domain_setU1.
have dc2: domain c' = csucc (domain c) by rewrite (succ_of_nat  qb).
have lc: slistp c'.
   split; [ apply:(fgraph_setU1 _ qa rb) | rewrite dc2; fprops].
have ec:echelon c'.
  split => // i; rewrite /slength dc2; move/(cltSleP qb) => /cle_eqVlt [].
    move => ->; rewrite (setU1_V_out _ qa rb); saw.
    move =>_ ; split; [ by apply/cge1P | apply:cleR; fprops].
    done.
  move => li; rewrite (setU1_V_in _ qa rb); first by apply: sa3.
  by apply /(NltP qb).
have dc3: slength c' = csucc m by  done.
have sep: \0c <c slength c'. 
  by rewrite /slength dc2; apply: succ_positive.
have atval: Vg c' m = J m \0c by rewrite (setU1_V_out _ qa rb).
have inval: forall k, k <c m -> Vg c' k = Vg c k.
  by move => k lkm; rewrite (setU1_V_in _ qa rb) //; apply /(NltP qb).
move: sc=> [kN kp [j ja jb]] kd.
split => //.  apply:(esize_prop2 ec).
  exists j; first by  rewrite /slength dc2; exact:(clt_leT ja (cleS qb)).
  by rewrite inval.
move => i; rewrite /slength dc2; move/(cltSleP qb) => /cle_eqVlt [].
   move => ->; rewrite atval; aw => _; apply: (proj1 kp).
by move => idc; rewrite inval //; apply: kd.
Qed.

Definition ech_shift n v:=
  Yo (P v = \0c) v (Yo (Q v = \0c) (J (P v +c n) \0c)
                       (J (P v +c n) (Q v +c n))).  

Definition ech_product1 f g n m i:=
   Yo (i <c n) (Vg f i)
    (Yo (i = n +c m) (J n (n +c m)) (ech_shift n (Vg g (i -c n)))).

Lemma  ech_product_prop1 f g n m i (v:= ech_product1 f g n m):
  natp n -> natp m ->
  [/\ i <c n -> v i = (Vg f i),  v(n +c m) =  (J n (n +c m)) &
      i <c m -> v (n +c i) =  ech_shift n (Vg g i)].
Proof.
rewrite /v /ech_product1 => nN mN.
have ha k: ~(n +c k <c n) by apply/cleNgt; exact: (Nsum_M0le _ nN).
split.
- by move => lin; Ytac0.
- by rewrite (Y_false (ha m)) Y_true.
move =>  lim. 
rewrite (Y_false (ha i)); Ytac h.
  move: lim =>[lim];case; exact: (csum_eq2l nN (NS_le_nat lim mN) mN h).
by rewrite csumC (cdiff_pr1 (NS_lt_nat lim mN) nN).
Qed.

Definition Ech_product f g :=
  let n := (slength f)  in let m := (slength g) in
  Lg (csucc (n +c m))(ech_product1 f g  n m).

Lemma Ech_product_prop f g (n := slength f) (m:= slength g)
  (h := Ech_product f g):
  echelon f ->
  echelon g ->
  \0c <c n ->
  [/\ echelon h,
      slength h = csucc (n +c m),
      esize h = cmax  (esize f) (esize g) &
      [/\ forall i, i <c n -> Vg h i = (Vg f i),
          Vg h (n +c m) =  (J n (n +c m)) ,
          forall i, i <c m -> Vg h (n +c i) =  ech_shift n (Vg g i) &
          forall i, n <=c i -> i <c n +c m ->
              Vg h i = ech_shift n (Vg g (i -c n))]].
Proof.
move=> echelon1 echelon2 np.
move: (echelon1)(echelon2) =>[[ha1 ha2] ha3] [[hb1 hb2] hb3].
have nz:=(nesym (proj2 np)).
have nN: natp n by exact (proj2 ha1).
have mN: natp m by exact (proj2 hb1).
have nmN := (NS_sum nN mN).
have snmN:= (NS_succ nmN).
have cp1:= (Nsum_M0le m nN).
have cp2 :=(cleR  (CS_nat nmN)).
have r0 i: i <c n +c m -> inc i (csucc (n +c m)).
   move => lin; apply/(NltP snmN).
   exact:(clt_leT lin (cleS nmN)).
have r1 i: i <c n -> Vg h i = Vg f i.
  move => lin.
  move: (ech_product_prop1 f g i nN mN) => [<- // _ _ ].
  rewrite /h /Ech_product LgV//; aw; apply: r0.
  exact:(clt_leT lin cp1).
have r2: Vg h (n +c m) = J n (n +c m).
  rewrite /h /Ech_product LgV; last by rewrite (succ_of_nat nmN);fprops.
  by case:(ech_product_prop1 f g n nN mN).
have r3 i: i <c m -> Vg h (n +c i) = ech_shift n (Vg g i).
  move =>  min; rewrite /h /Ech_product LgV//.
    by move: (ech_product_prop1 f g i nN mN) => [ _ _ ->].
 apply: r0;apply:(csum_Meqlt nN min).
have r4 i: n <=c i -> i <c n +c m -> Vg h i = ech_shift n (Vg g (i -c n)).
  move => i1 i2; move:(NS_lt_nat i2 nmN)(cdiff_pr i1) => iN i3.
  move: i2; rewrite -{1 2} i3 => i2.
  by move: (csum_lt2l nN (NS_diff n iN) mN i2) => i4; rewrite r3.
have r5: slength h = csucc (n +c m).
  by rewrite /slength /h /Ech_product Lgd.
have r6: sub (range h) (Nat \times Nat).
  move => t /Lg_range_P [b bs ->].
  move: (ech_product_prop1  f g b nN mN) => [sa sb sc].
  move/(NltP snmN): bs => /(cltSleP nmN) /cle_eqVlt [].
    by move => ->; rewrite sb; apply: setXp_i.
  move => lbnm; case:(cleT_el (CS_nat nN) (proj31_1 lbnm)) => lbn; last first.
    rewrite (sa lbn); apply: ha2; apply /(range_gP (proj1 ha1)); exists b=> //.
    by apply /(NltP nN).
  move: (cdiff_pr lbn) => d1.
  have bN:= (NS_lt_nat lbnm nmN).
  rewrite - d1 in lbnm; move: (csum_lt2l nN (NS_diff n bN) mN lbnm) => ha.
  move: (ech_product_prop1  f g (b -c n)  nN mN) => [_ _  sc'].
  rewrite  - d1 (sc' ha); rewrite /ech_shift. 
  have vr : inc (Vg g (b -c n)) (range g).
    by apply /(range_gP (proj1 hb1)); exists (b-c n) => //;apply /(NltP mN).
  move: (hb2 _ vr) =>w.
  move/setX_P: (w)=>[]; set aa := P _; set bb :=Q _ => [qa qb qc].
  Ytac h1 => //; Ytac h2.
    apply:(setXp_i (NS_sum qb nN) NS0).
    apply:(setXp_i (NS_sum qb nN) (NS_sum qc nN)).
have r7: domain h = csucc (n +c m)  by rewrite /h/Ech_product; aw.
have r8: slist_E h (Nat \times Nat).
  split => //; split; [ apply:Lg_fgraph | ue].
have r9: echelon h.
  split => // i; rewrite r5; move => /(cltSleP nmN) /cle_eqVlt [].
    move => -> /=; rewrite r2; aw;split.
      by move/csum_nz => [/nz]. 
    move => ha hb; split; split => //; apply/cge1P => //.
    by apply:(card_ne0_pos (CS_nat nmN)).
  move => lbnm; case:(cleT_el (CS_nat nN) (proj31_1 lbnm)) => lbn; last first.
    by rewrite (r1 _ lbn); apply: ha3.
  move:(NS_lt_nat lbnm nmN)(cdiff_pr lbn) => iN i3.
  move: lbnm; rewrite -{1 2 3} i3 => i2.
  move: (csum_lt2l nN (NS_diff n iN) mN i2) => i4.
  move:(hb3 _ i4); rewrite (r3 _ i4) /ech_shift /=. 
  set a := P _; set b := Q _; move => [ha hb].
  case:(equal_or_not a \0c) => az; Ytac0.
    split; first by move/ha => []; rewrite az => a1; move:(cltNge clt_01 a1).
    by move => _; case.
  have h0 c: ech_good c (i -c n) -> ech_good (c +c n) i.
    move => [hc hd]; split; first exact: (cleT hc (csum_M0le n (proj32 hc))).
    by rewrite - i3 csumC; apply: csum_Meqle.
  case:(equal_or_not b \0c) => bz; Ytac0; aw; split.
  - by move => _; move: (ha bz); apply: h0.
  - by case.
  - by move /csum_nz => [_ /nz].
  - by move:(hb bz az) => [hc hd] _ _; split; apply: h0.
split => //.
move: (esize_prop1 echelon1 np); set N := esize f.
move => [NN Np [ja ja1 ja2] ja3].
case: (equal_or_not m \0c) => mz.
  have max0: cmax N \0c  = N. 
    by rewrite (cmax_yx (proj1 Np)).
  rewrite (esize_empty echelon2 mz) max0.
  have s0: slength h = csucc n.
    by rewrite /slength r7 mz (csum0r (CS_nat nN)).
  apply: (esize_prop2 r9); rewrite s0.
    exists ja; [exact:(clt_leT ja1 (cleS nN)) | by rewrite r1].
  move => j /(cltSleP nN) /cle_eqVlt [].
    move ->. move: r2. rewrite mz (csum0r (CS_nat nN)) => ->; aw => //.
  move => jn; rewrite (r1 _ jn); exact (ja3 _ jn).
have mp:= (card_ne0_pos (CS_nat mN) mz).
move: (esize_prop1 echelon2 mp); set M := esize g.
move => [MN Mp [ka ka1 ka2] ka3].
move:(cmax_p1 (proj32_1 Np) (proj32_1 Mp)) => [max1 max2].
apply: (esize_prop2 r9).
  have ja4: ja <c slength h.
   rewrite r5; exact: (clt_leT (clt_leT ja1 cp1) (cleS nmN)).
  have ka4: n +c ka <c slength h.
    rewrite r5; exact: (clt_leT (csum_Meqlt nN ka1) (cleS nmN)).
  rewrite /cmax/Gmax; case: (p_or_not_p (N <=c M)) => lnm; Ytac0.
     exists (n +c ka) => //;rewrite (r3 _ ka1).
     by rewrite /ech_shift ka2 pr1_pair (Y_true (erefl \0c)). 
  by exists ja => //;rewrite r1.
move => j; rewrite r5; move => /(cltSleP nmN) /cle_eqVlt [].
  by move => -> /=; rewrite r2; aw.
move => ljnm; case:(cleT_el (CS_nat nN) (proj31_1 ljnm)) => ljn; last first.
   rewrite (r1 _ ljn) => anz; exact: (cleT (ja3 _ ljn anz) max1).
move:(NS_lt_nat ljnm nmN)(cdiff_pr ljn) => iN i3.
move: ljnm; rewrite -{1 2 3} i3 => i2.
move: (csum_lt2l nN (NS_diff n iN) mN i2) => i4.
rewrite (r3 _ i4) /ech_shift; set a:= (P (Vg g _)); set b := Q _.
case:(equal_or_not a \0c) => az; Ytac0. 
  move => _; exact: (cleT  (ka3 _ i4 az) max2).
have anz : a +c n <> \0c by move/csum_nz => [].
by case:(equal_or_not b \0c) => bz; Ytac0; aw.
Qed.                  


Fixpoint Tree_to_echelon t :=
  match t with
    | Tbase n  => Ech_base (nat_to_B n.+1)
    | Tpowerset t' =>  Ech_powerset (Tree_to_echelon t')
    | Tproduct t' t'' =>
      Ech_product (Tree_to_echelon t') (Tree_to_echelon t'')
end.

Definition tree_to_echelon x := tree_rec
  (fun n => Ech_base (csucc n))
  (fun t => Ech_powerset t)
  (fun t t'  => Ech_product  t t') x.

Lemma tree_to_echelon_E (f:=tree_to_echelon) :
  [/\ forall n, natp n -> f (Tb n) =  Ech_base (csucc n),
    forall t, treep t -> f (Tp t) =  Ech_powerset (f t) &
    forall t t', treep t -> treep t' ->
                f (Tx t t') =   Ech_product (f t) (f t')].
Proof.
rewrite /f/tree_to_echelon; split.
- by move => n nN;rewrite tree_recdef_pb'.
- by move => x tp; rewrite tree_recdef_pp.
- by move => t t' tp tp'; rewrite tree_recdef_px.
Qed.

Lemma tree_to_echelon_prop2 t:
  tree_to_echelon (Tree_to_tree t) = Tree_to_echelon t.
Proof.
have H0 x: treep (Tree_to_tree x) by case: (Tree_to_tree_prop x).
elim:t.
- by move => n; rewrite (proj31 tree_to_echelon_E _ (nat_to_B_Nat n)) /=.
- by move => e Hr; rewrite /= (proj32 tree_to_echelon_E _ (H0 e)) Hr.
- move => e Hr1 e' Hr2.
  by rewrite /= (proj33 tree_to_echelon_E _ _  (H0 e) (H0 e')) Hr1 Hr2.
Qed.  


Lemma tree_to_echelon_ok t (c := tree_to_echelon t): treep  t ->
  [/\ echelon c, \0c <c slength  c & esize c = csucc (tree_size t)].
Proof.
rewrite /c{c}; move:t; apply: tree_ind.
- move => n nN. 
  move: (Ech_base_prop (NS_succ nN) (succ_positive n)) => [ea eb ec ed].
  rewrite (proj31 tree_to_echelon_E _ nN); split => //.
  by rewrite ed (proj31 tree_size_p _ nN).
- move => x tx [h1 h2 h3].
  move:(Ech_powerset_prop h1 h2); rewrite h3; move  => [ha hb hc _ _].
  rewrite (proj32 tree_to_echelon_E _ tx) hc  (proj32 tree_size_p _ tx) hb.
  split => //; apply: succ_positive.
- move => x x' tx tx'  [h1 h2 h3]  [h1' h2' h3'].
  rewrite (proj33 tree_to_echelon_E _ _ tx tx') (proj33 tree_size_p _ _ tx tx').
  move:(Ech_product_prop h1 h1' h2) => [ra rb rc _]; rewrite rc;split => //.
    by  rewrite rb; apply: succ_positive.
  by rewrite h3 h3' cmax_succ //;apply: CS_nat; apply:NS_tree_size.
Qed.

Section EchelonRecdef.


Variable h1: Set -> Set.
Variable h2: Set -> Set.
Variable h3: Set -> Set -> Set.

Definition erecdef_combine h1 h2 h3 :=
  fun f a b => Yo (a = \0c) (h1 b)
                  (Yo (b = \0c) (h2  (Vl f a)) (h3 (Vl f a) (Vl f b))). 

Definition echelon_recdef_prop c  (p: Set -> Set -> Set -> Set):=
   forall g1 g2 i,
   i <c  slength c ->
   (forall j, j <c i -> Vg g1 j = Vg g2 j) -> 
   p  g1 (P (Vg c i)) (Q (Vg c i)) = p  g2 (P (Vg c i)) (Q (Vg c i)).

Lemma erecdef_prop1 c: 
  echelon c -> echelon_recdef_prop c (erecdef_combine h1 h2 h3).
Proof.
move => [[ka kb] kc] g1 g2 i lim Hr.
rewrite /erecdef_combine.
move: (proj2 ka) => mN.
have iN:= (NS_lt_nat lim mN).
have aux x: ech_good x i -> (Vl g1 x) = (Vl g2 x).
   move => [/cge1P  ra' rb']; apply: Hr.
   have xN:=(NS_le_nat rb' iN).
   have [cpN cpv]:= (cpred_pr xN  (nesym (proj2 ra'))).
   by apply/(cleSltP cpN); rewrite - cpv.
move:(kc _ lim) => [kc1 kc2].
case: (p_or_not_p (P (Vg c i) = \0c)) => ca; Ytac0; Ytac0; first  by done.
case: (p_or_not_p (Q (Vg c i) = \0c)) => cb; Ytac0; Ytac0.
  by rewrite (aux _ (kc1 cb)).
by move: (kc2 cb ca) => [ua ub]; rewrite !aux.
Qed.


Definition echelon_recdef c (p :=  erecdef_combine h1 h2 h3) :=
  restr (graph (transfinite_defined Nat_order
     (fun u => (p  (graph u) (P (Vg c (source u))) (Q (Vg c (source u)))))))
        (slength c).

  

Lemma erecdef_prop c (m := slength c)(f := echelon_recdef c)
      (p :=  erecdef_combine h1 h2 h3):
  echelon c ->
  [/\ fgraph f, domain f = m &
   forall i, i <c m -> Vg f i = p f (P (Vg c i)) (Q (Vg c i))].
Proof.
move => ec; move: (ec)=> [[ka kb] kc].
rewrite /f /echelon_recdef{f}; set g := fun u:Set => _.
move: Nat_order_wor => [wor sr].
move: (transfinite_defined_pr g wor).
set f1 := (transfinite_defined Nat_order g).
rewrite /transfinite_def sr /g; move => [ra rb rc]. 
have sa i: natp i -> Vf f1 i = p  (restr (graph f1) i)(P (Vg c i))(Q (Vg c i)).
  move => iN; rewrite (rc _ iN)  /restriction1.
  by rewrite (segment_Nat_order iN) (NintE iN); aw.
move: (slength_nat ka); rewrite -/m => mN.
set f := restr _ _.
have ha: fgraph f by apply: restr_fgraph.
have hb: domain f = m by rewrite /f restr_d.
split => // i lim.
have iN:= (NS_lt_nat lim mN).
have il: inc i m by apply /(NltP mN). 
rewrite /f (restr_ev _ il) -/(Vf _ _) (sa _ iN);
apply: (erecdef_prop1 ec) => // j ji.
have ijm: inc j m by apply /(NltP mN); apply: (clt_ltT ji lim).
have iji: inc j i by apply /(NltP iN).
by rewrite !LgV.
Qed.


Lemma erecdef_unique c f (m := slength c) (p :=  erecdef_combine h1 h2 h3):
  echelon c ->
  slistpl f m -> 
  (forall i, i <c m -> Vg f i = p f (P (Vg c i)) (Q (Vg c i))) ->
  f =  echelon_recdef c.
Proof.
move => pa [pb pc] pd.
move: (erecdef_prop  pa); set g := (echelon_recdef c).
move => [qa qb qc].
have fgf: fgraph f by move: pb => [].
have dfdg: domain f = domain g by rewrite  qb.
have mN :=  (proj2(proj1 (proj1 pa))).
apply: fgraph_exten => // i; rewrite dfdg qb -/m => im. 
have iN:=(NS_inc_nat mN im).
move/(NltP mN):im.
move: i iN;apply: Nat_induction1 => n nN Hr lt.
rewrite (pd _ lt) (qc _ lt).
apply:(erecdef_prop1 pa) => // => j ljn.
apply: Hr => //; exact: (clt_ltT ljn lt).
Qed.


Lemma erecdef_prop2 c (m := slength c)(f :=  echelon_recdef c)
   (n:=  esize c): 
  echelon c -> forall i, i <c m ->
  let a:= P (Vg c i) in let b := Q (Vg c i) in
  [/\ a = \0c -> [/\ \1c <=c b, b <=c n & Vg f i = (h1 b)],
      b = \0c -> [/\ \1c <=c a, a <=c i & Vg f i = h2 (Vl f a) ]
    & a <> \0c -> b <> \0c -> [/\ \1c <=c a, a <=c i, \1c <=c b, b <=c i &
   Vg f i = h3 (Vl f a) (Vl f b)]].
Proof.
move => ec i lim ; move: (erecdef_prop ec); rewrite -/f.
move => [ha hb hc] /=; rewrite (hc _ lim) /erecdef_combine.
move: (esize_prop1 ec (cle_ltT (cle0x (proj31_1 lim)) lim)).
rewrite -/n -/m; move=> [na nb nc nd].
move: ((proj2 ec) _ lim); simpl;set a := P _; set b := Q _; move=> [ia ib].
have hu: b = \0c -> a <> \0c.
  by move => bz az; move:(proj1 (ia bz)); rewrite az=> w; case:(cltNge clt_01).
split. 
- move=> az; rewrite az; Ytac0.
  by have bn:=(nd _ lim az); split =>//; apply: (cge1 (proj31 bn)) => /hu.
- by move => bz; move:(ia  bz) (hu bz) => [a1 a2] a3; split => //;Ytac0; Ytac0.
- move => az bz; move:(ib bz az) => [[q1 q2][q3 q4]].
  by split => //; Ytac0; Ytac0.
Qed.

Lemma erecdef_unique1 c f (m := slength c):
  echelon c ->
  slistpl f m -> 
  (forall i, i <c m ->
    let a:= P (Vg c i) in let b := Q (Vg c i) in
    [/\ a = \0c -> Vg f i = h1 b,
        b = \0c -> Vg f i = h2 (Vl f a) 
      & a <> \0c -> b <> \0c -> Vg f i = h3 (Vl f a) (Vl f b)]) ->
  f = echelon_recdef c.
Proof.
move => ha hc hd.
have he:= (erecdef_prop ha).
apply: erecdef_unique => // i lim.
rewrite / erecdef_combine; move:(hd _ lim).
set a := P _; set b := Q _; move => [ka kb kc].
case: (p_or_not_p (a = \0c)) => az; Ytac0; first by apply: (ka az).
case: (p_or_not_p (b = \0c)) => bz; Ytac0; first by apply: (kb bz).
by apply: kc.
Qed.

Lemma erecdef_restr c n:
   echelon c -> n <=c slength c ->
   echelon_recdef (restr c n) = restr (echelon_recdef c) n.
Proof.
move => ha hb; symmetry.
move: (ha) => [[[pa pb] pc] pd].
have dr: domain (restr c n) = n by aw.
have sid: sub n (domain c) by exact:(proj33 hb).
have nN := NS_le_nat hb pb.
have hc: slist_E (restr c n) (Nat \times Nat).
  split; first by split; fprops;  rewrite dr.
  exact: (sub_trans (restr_range1 pa sid) pc).
have hd: echelon (restr c n).
  split => // i; rewrite /slength dr => lin.
  have in': inc i n by apply/(NltP nN).
  by rewrite LgV//; apply: pd; apply: (clt_leT lin hb).
have he:slistpl (restr (echelon_recdef c) n) (slength (restr c n)).
  by rewrite /slistpl /slength !Lgd; split => //; split=> //;fprops; aw.
apply: (erecdef_unique hd he); aw => i lin.
have in': inc i n by apply/(NltP nN).
have iN:= (NS_lt_nat lin nN).
have lin': i <c slength c by exact: (clt_leT lin hb).
move: (erecdef_prop ha) => [ra rb rc].
rewrite LgV // (rc _ lin'); rewrite LgV //.
apply:erecdef_prop1 => // j ji.
by move/(NltP nN):(clt_ltT ji lin) => ljn; rewrite [in RHS] LgV//.
Qed.


Lemma echelon_recdef_extent2 c c' i:
  echelon c -> echelon c' -> i <=c slength c -> i <=c slength c' ->
  i <> \0c ->
  (forall k, k<c i -> Vg c k = Vg c' k) -> 
  Vl (echelon_recdef c) i = Vl (echelon_recdef c') i.
Proof.
move => ec1 ec2 k1 k2 ip sv.
have iN:=(NS_le_nat k1 (proj2 (proj1 (proj1 ec1)))).
have lii: inc (cpred i) i by apply/(NltP iN); exact:(cpred_lt iN ip).
have: echelon_recdef (restr c i) =  echelon_recdef (restr c' i).
  congr echelon_recdef; apply: fgraph_exten; aww.
  by move => j ji /=; rewrite ! LgV//; apply: sv; apply/(NltP iN).
rewrite (erecdef_restr ec1 k1) (erecdef_restr ec2 k2).
by move/(f_equal (fun z => Vl z i)); rewrite /Vl LgV // => ->; rewrite LgV.
Qed.

Definition echelon_recdef_last c := Vl (echelon_recdef c) (slength c).

Lemma erecdef_base n (c := Ech_base n):
  natp n -> \0c <c n -> echelon_recdef_last c = h1 n.
Proof.
move => sa sb.
move: (Ech_base_prop sa sb) =>[ha hb hc hd].
have slc: slength c = \1c; rewrite /slength /c/Ech_base; aw; trivial.
rewrite /echelon_recdef_last /Vl slc cpred1.
have sz: \0c <c slength c by rewrite slc; exact : clt_01.
move:(proj31 (erecdef_prop2 ha sz)); rewrite hb; aw => h.
exact: (proj33 (h (erefl \0c))).
Qed.



Lemma erecdef_powerset c (c' := Ech_powerset c):
  echelon c -> \0c <c slength c ->
  echelon_recdef_last c' = h2 ( echelon_recdef_last c).
Proof.
rewrite/echelon_recdef_last => ec cp.
move:(Ech_powerset_prop ec cp) => [ha hb hc hd he].
rewrite /c' hb /Vl (cpred_pr1 (proj32_1 cp)).
have p1: (slength c) <c slength (Ech_powerset c). 
  rewrite hb; apply: cltS; exact: (proj2 (proj1 (proj1 ec))).
move: (proj32 (erecdef_prop2 ha p1)); rewrite hd; aw => hh.
move: (hh (erefl \0c))  => [ka kb ->]; congr h2.
apply:(echelon_recdef_extent2 ha ec (proj1 p1) kb (nesym (proj2 cp)) he).
Qed.
  

Lemma erecdef_product c c' (c'' := Ech_product c c'):
  echelon c -> echelon c' -> \0c <c slength c -> \0c <c slength c' ->
  echelon_recdef_last c'' = h3 (echelon_recdef_last c) (echelon_recdef_last c').
Proof.
rewrite/echelon_recdef_last => ec ec' cp cp'.
move:(Ech_product_prop ec ec' cp) => [ra rb rc [rd re rf rg]].
move:(proj2 (proj1 (proj1 ec))) (proj2 (proj1 (proj1 ec'))) => s1N s2N.
move: (CS_nat s1N) (CS_nat s2N) => cs1 cs2.
set s := (slength c).
set s' := (slength c'); move:(nesym (proj2 cp')) => s2nz.
move: (cpred_pr s2N s2nz); rewrite -/(slength c');move => [qa qb].
have eqa:cpred (s +c s') = s +c cpred s'.
  by rewrite /s' {1} qb (csum_via_succ _ (CS_nat qa)) (cpred_pr1 (CS_sum2 _ _)).
have qc: s <=c slength c''.
  by rewrite rb -(csum_via_succ _ cs2);apply:csum_M0le cs1.
have qd: (cpred (slength c'')) = s +c s' by rewrite rb cpred_pr1; fprops.
have pa: s <> \0c by exact:(nesym (proj2 cp)).
have pb: s +c s' <> \0c by case/csum_nz.
have sl1:  (cpred (slength c'')) <c (slength c'').
  apply:(cpred_lt (proj2 (proj1(proj1 ra))));rewrite [domain _]rb.
  apply: succ_nz.
move:(proj33 (erecdef_prop2 ra sl1)); rewrite qd re /Vl; aw => h11.
move:(h11 pa pb) => [pc pd pe pf pg] {h11};rewrite /Vl qd pg; congr h3.
  apply:(echelon_recdef_extent2 ra ec qc (cleR cs1) (nesym (proj2 cp))).
  by move => k kl; rewrite rd.
clear pa pb pc pd pe pf pg.
rewrite eqa.
have: cpred s' <c s' by exact:(cpred_lt s2N s2nz).
move: qa; move: (cpred s'); apply: Nat_induction1.
move => i iN Hr lis1.
move:( erecdef_prop2 ec' lis1) => [ca cb cc].
have lis2: (s +c i) <c slength (Ech_product c c').
  rewrite rb -/s - (csum_via_succ _ cs2); apply:(csum_Meqlt s1N).
  exact: (clt_leT lis1 (cleS s2N)).
move:(erecdef_prop2 ra lis2)  => [].
rewrite (rf _ lis1) /ech_shift.
case: (equal_or_not (P (Vg c' i)) \0c) => az; Ytac0.
  by move => hu _ _; move: (hu az)  (ca az)  => [_ _ ->] [_ _ ->].
case: (equal_or_not (Q (Vg c' i)) \0c) => bz; Ytac0.
  move => _ hu _; move: hu; aw => hu.
  move: (hu (erefl \0c)) (cb bz) => [p1 p2 ->] [p3 p4 ->].
  rewrite /Vl.
  move: (cpred_pr6' iN p3 p4) => [ua ub uc].
  have ->: cpred (P (Vg c' i) +c slength c) = s +c cpred (P (Vg c' i)).
    rewrite {1} ub csumC (csum_via_succ _ (CS_nat ua)) cpred_pr1; fprops.
  rewrite Hr //; apply: (clt_ltT uc lis1).
move => _ _ hu; move: hu; aw => hu.
have az': P (Vg c' i) +c slength c <> \0c by  case/csum_nz.
have bz': Q (Vg c' i) +c slength c <> \0c by  case/csum_nz.
move: (cc az bz) => [p1 p2 p3 p4 ->].
move: (hu az' bz') => [p1' p2' p3' p4' ->].
rewrite /Vl.
move: (cpred_pr6' iN p1 p2) => [ua ub uc].
have ->: cpred (P (Vg c' i) +c slength c) = s +c cpred (P (Vg c' i)).
  rewrite {1} ub csumC (csum_via_succ _ (CS_nat ua)) cpred_pr1; fprops.
move: (cpred_pr6' iN p3 p4) => [ua' ub' uc'].
have ->: cpred (Q (Vg c' i) +c slength c) = s +c cpred (Q (Vg c' i)).
  rewrite {1} ub' csumC (csum_via_succ _ (CS_nat ua')) cpred_pr1; fprops.
move: (clt_ltT uc lis1) (clt_ltT uc' lis1) => lt1 lt2.
rewrite Hr // Hr //.
Qed.

End EchelonRecdef.



Definition echelon_to_trees :=  echelon_recdef (fun b => Tb (cpred b)) Tp Tx.

Lemma echelon_to_trees_prop c (m := slength c)(f := echelon_to_trees c)
      (n := esize c):
  echelon c ->
  [/\ fgraph f, domain f = m,
      forall i, i <c m -> treep (Vg f i) &
      forall i, i <c m -> 
        let a:= P (Vg c i) in let b := Q (Vg c i) in
         [/\ a = \0c -> [/\ \1c <=c b, b <=c n & Vg f i =  Tb (cpred b)], 
           b = \0c -> [/\ \1c <=c a, a <=c i &  Vg f i = Tp (Vl f a)]
          & a <> \0c -> b <> \0c -> [/\ \1c <=c a, a <=c i, \1c <=c b, b <=c i 
               & Vg f i = Tx (Vl f a) (Vl f b)]]].
Proof.
move => ha.
move: (erecdef_prop (fun b => Tb (cpred b)) Tp Tx ha) => [hc hd _].
move: (erecdef_prop2 (fun b => Tb (cpred b)) Tp Tx ha) => he.
split => //.
move => i lim; move:(NS_lt_nat lim (proj2 (proj1 (proj1 ha)))) => iN.
move: i iN lim; apply: Nat_induction1.
move => i iN Hr lim.
move:(he _ lim) => [ra rb rc].
case: (equal_or_not (P (Vg c i)) \0c) => az.
  move:(ra az) => [sa sb ->].
  apply: (TS_base (proj31(cpred_pr6' (NS_esize ha)  sa sb))).
case: (equal_or_not (Q (Vg c i)) \0c) => bz.
  move:(rb bz) => [sa sb ->]; have sc := (proj33(cpred_pr6' iN sa sb)).
  apply:TS_powerset; apply: Hr => //; exact:(clt_ltT sc lim).
move:(rc az bz) => [sa sb sa' sb' ->].
have sc := (proj33(cpred_pr6' iN sa sb)); have sd:= (clt_ltT sc lim).
have sc' := (proj33(cpred_pr6' iN sa' sb')); have sd':= (clt_ltT sc' lim).
by apply:TS_product; apply:Hr.
Qed.


Lemma ET_val1 c i (f := echelon_to_trees c):
  echelon c -> i <c (slength c) -> P (Vg c i) = \0c -> 
  exists n,  Q (Vg c i) = csucc (nat_to_B n) /\ 
  Vg f i = Tree_to_tree (Tbase n).
Proof.
move => ha hb az.
move: (echelon_to_trees_prop ha) => [_ _ hd hc].
move: (hc _ hb) => [he _ _] {hc}; move: (he az).
move => [qa qb qc].
have bN:= (NS_le_nat qb (NS_esize ha)).
move: (cpred_pr6' (NS_esize ha) qa qb) => [sa sb sc].
move:(nat_to_B_surjective sa) => [n nv].
by  exists n; rewrite /f /= qc {1} sb nv. 
Qed.

Lemma ET_val2 c i (f := echelon_to_trees c):
  echelon c -> i <c (slength c) -> Q (Vg c i) = \0c -> 
  exists2 E, Tree_to_tree E = (Vl f (P (Vg c i))) &
              Tree_to_tree (Tpowerset E) = Vg f i.
Proof.
move => ha hb az.
move: (echelon_to_trees_prop ha) => [_ _ hd hc].
move: (hc _ hb) => [_ he2 _] {hc}; move: (he2 az) => [qa qb qc] {he2}.
have mN:= (proj2 (proj1 (proj1 ha))).
have iN:= (NS_lt_nat hb mN).
set a :=  P (Vg c i). 
move: (cpred_pr6' iN qa qb) => [sa sb sc].
move: (Tree_to_tree_surjective (hd _(clt_ltT sc hb))) => [e ev].
by exists e => //; rewrite  /f qc /= /Vl ev.
Qed.

Lemma ET_val3 c i (f := echelon_to_trees c)
      (a := (P (Vg c i))) (b := Q (Vg c i)):
  echelon c ->  i <c (slength c) -> a <> \0c -> b <> \0c -> 
  exists E F, [ /\  Tree_to_tree E = Vl f a,
                   Tree_to_tree F = Vl f b&
                   Tree_to_tree (Tproduct E F) = Vg f i ].
Proof.
move => ha hb az bz.
move: (echelon_to_trees_prop ha) => [_ _  hd hc].
move: (hc _ hb) => [_ _ he3] {hc}; move: (he3 az bz) => []{he3}. 
rewrite -/a -/b => ha1 ha2 hb1 hb2 hf.
have mN:= (proj2 (proj1 (proj1 ha))).
have iN:= (NS_lt_nat hb mN).
move: (cpred_pr6' iN ha1 ha2) => [sa sb sc].
move: (cpred_pr6' iN hb1 hb2) => [sa' sb' sc'].
move: (Tree_to_tree_surjective (hd _(clt_ltT sc hb))) => [e ev].
move: (Tree_to_tree_surjective (hd _(clt_ltT sc' hb))) => [e' ev'].
by exists e,e'; rewrite /f hf /Vl ev ev'. 
Qed.

(**   Evaluating an echelmon on a set *)

Definition echelon_value c E :=
  echelon_recdef  (fun b => (Vl E b)) powerset product c.

Definition echelon_of_base c E := 
  Vl (echelon_value c E) (slength c).

Lemma echelon_of_baseE c E:
  echelon_of_base c E =
  echelon_recdef_last (fun b => (Vl E b)) powerset product c.
Proof. by []. Qed.


Lemma echelon_value_prop c E i (m := slength c)(f :=  echelon_value c E)
   (n:=  esize c):
  echelon c -> i <c m ->
  let a:= P (Vg c i) in let b := Q (Vg c i) in
  [/\ a = \0c -> [/\ \1c <=c b, b <=c n & Vg f i = (Vl E b)],
      b = \0c -> [/\ \1c <=c a, a <=c i & Vg f i = \Po (Vl f a) ]
    & a <> \0c -> b <> \0c -> [/\ \1c <=c a, a <=c i, \1c <=c b, b <=c i &
   Vg f i = (Vl f a) \times (Vl f b)]].
Proof. by move => h; apply:erecdef_prop2. Qed.



Fixpoint Tree_value E e:=
  match e with
    | Tbase n  => Vg E (nat_to_B n)
    | Tpowerset e' => \Po (Tree_value E e')
    | Tproduct e' e'' =>
      (Tree_value E e') \times (Tree_value E e'')
end.



Definition tree_value E x := tree_rec
  (fun n => Vg E n)
  (fun t => \Po t)
  (fun t t'  => t \times t') x.

Lemma tree_value_prop E:
  [/\ (forall n, natp n -> tree_value E (Tb n) = Vg E n),
     (forall x, treep x -> tree_value E (Tp x) = \Po (tree_value E x))&
     (forall x y, treep x -> treep y -> 
        tree_value E (Tx x y) = (tree_value E x) \times (tree_value E y))].
Proof.
rewrite /tree_value;split.
- by move => n nN; rewrite tree_recdef_pb'.
- by move => t tp ; rewrite  tree_recdef_pp.
- by move => t t' tp tp' ; rewrite  tree_recdef_px.
Qed.

Lemma Tree_value_compat E e:
  tree_value E (Tree_to_tree e) = Tree_value E e.
Proof.
move:(tree_value_prop E) => [ha hb hc].
have H0 x: treep (Tree_to_tree x) by case: (Tree_to_tree_prop x).
elim:e.
- by move => n /=; rewrite ha //; apply: nat_to_B_Nat.
- by move => t h /=; rewrite -h hb //. 
- by move => t h t' h' /=; rewrite - h - h' hc //.
Qed.


Lemma tree_value_extent T E E': treep T -> 
  (forall i, i<=c (tree_size T) -> Vg E i = Vg E' i) ->
  tree_value E T = tree_value E' T.
Proof.
set P := (tree_value_prop E) ; set P' :=  (tree_value_prop E').
move: T; apply:tree_ind.
- move => n nN  h.
  rewrite(proj31 P n nN) (proj31 P' n nN); apply: h.
  rewrite (proj31 tree_size_p _ nN); exact: (cleR (CS_nat nN)).
- move => x tp h1; rewrite (proj32 tree_size_p x tp) => h2.
  by rewrite(proj32 P x tp) (proj32 P' x tp); rewrite (h1 h2).
- move => x x' tp tp'.
  rewrite (proj33 tree_size_p x x' tp tp') => h1 h2 h3. 
  rewrite (proj33 P x x' tp tp') (proj33 P' x x' tp tp').
  move:(Nmax_p1 (NS_tree_size tp) (NS_tree_size tp'))=> [ma mb mc].
  have q1: forall i, i <=c tree_size x -> Vg E i = Vg E' i.
    move => i li1; exact: (h3 _ (cleT li1 mb)).
  have q1': forall i, i <=c tree_size x' -> Vg E i = Vg E' i.
    move => i li1; exact: (h3 _ (cleT li1 mc)).
  by rewrite h1 // h2.
Qed.


Lemma echelon_of_base_of_tree t E: treep t ->
   echelon_of_base (tree_to_echelon t) E = tree_value E t.
Proof.
move:(tree_value_prop E) => [ha hb hc].
move: tree_to_echelon_E => [qa qb qc].
move: t;apply: tree_ind.
- move => n nN.
  move:(NS_succ nN) (succ_positive n) => hu hv.
  rewrite (ha _ nN) (qa _ nN) echelon_of_baseE erecdef_base // /Vl.
  by rewrite (cpred_pr1 (CS_nat nN)).
- move => x tx Hr.
  move:(tree_to_echelon_ok tx) => [sa sb sc].
  by rewrite (qb _ tx) (hb _ tx) echelon_of_baseE erecdef_powerset // - Hr //.
- move => x x' tx tx' Hx Hx'.
  move:(tree_to_echelon_ok tx) => [sa sb sc].
  move:(tree_to_echelon_ok tx') => [sa' sb' sc'].
  rewrite (qc _ _ tx tx')  (hc _ _ tx tx').
  by rewrite echelon_of_baseE erecdef_product // -Hx// - Hx' //.
Qed.



Lemma tree_val_ne n  E : (forall i, i <c n -> nonempty (Vg E i)) ->
  forall t, treep t -> tree_size t <c n -> nonempty(tree_value E t).
Proof.
move => hb.
apply:tree_ind.
+ move => i iN.
  rewrite (proj31 tree_size_p i iN) (proj31 (tree_value_prop E) i iN).
  by apply: hb.
+ move => x tx _ _; rewrite (proj32 (tree_value_prop E) _ tx).
  by exists emptyset; apply: setP_0i.
+ move => x x' tx tx' hc hd.
  rewrite(proj33 tree_size_p _ _ tx tx')(proj33 (tree_value_prop E) _ _ tx tx').
  move => he.
  move: (Nmax_p1 (NS_tree_size tx) (NS_tree_size tx')) => [sa sb sc].
  move:(rep_i (hc (cle_ltT sb he))); set u := rep _ =>  e1.
  move:(rep_i (hd (cle_ltT sc he))); set v := rep _ =>  e2.
  by exists (J u v); apply: setXp_i.
Qed. 


Lemma powerset_injective: injective powerset.
Proof.
move => x y eq1; apply:extensionality.
  by move:(setP_Ti x); rewrite eq1 => /setP_P.
by move:(setP_Ti y); rewrite - eq1 => /setP_P.
Qed.


Lemma product_injective A B C D:
  nonempty (C \times D) -> A\times B = C\times D -> A = C /\ B = D.
Proof.
move => [x /setX_P [pa pb pc]]  eq1.
move: (setXp_i pb pc); rewrite - eq1 => /setXp_P [pd pe].
split; set_extens t => h.
- by move:(setXp_i h pe); rewrite  eq1; case /setXp_P.
- by move:(setXp_i h pc); rewrite - eq1; case /setXp_P.
- by move:(setXp_i pd h); rewrite eq1; case /setXp_P.
- by move:(setXp_i pb h); rewrite - eq1; case /setXp_P.
Qed.


Lemma not_a_powerset3 x: \3c <> powerset x.
Proof.
move => h.
have i12: inc \1c \2c by exact: set2_2.
have: inc \2c \3c by apply/(NltP NS3); exact: (cltS NS2).
rewrite h => /setP_P => h'; move: (h' _ i12) => h''.
have : inc (singleton \1c) \3c by rewrite h; apply/setP_P => t /set1_P ->.
rewrite /card_three (succ_of_nat NS2) => /setU1_P; case.
  have hx := (set1_1 \1c).
  case/set2_P => hy;  move: hx; rewrite hy; first by move => /in_set0.
  by move /set1_P => hz; move:(set1_1 \0c); rewrite -/card_one hz => /in_set0.
move => hy.
move: (set2_1 \0c \1c). rewrite -/card_two -hy => /set1_P bad.
by case: card1_nz.
Qed.


Lemma powerset_not_product x y z:  powerset x <> y \times z.
Proof.
move => eq1. move:(setP_0i x); rewrite eq1 => /setX_pair.
rewrite /pairp kpairE /kpair_def;set t := singleton _ => h.
have /in_set0 //: inc t emptyset by rewrite - h; apply:set2_1.
Qed.

Lemma not_a_product1 x y: \1c <> x \times y.
Proof. 
by rewrite /card_one - setP_0; exact:powerset_not_product.
Qed.

Lemma clt_3: [/\ \0c <c \3c, \1c <c \3c & \2c <c \3c]. 
Proof.
have ha:=(cltS NS2).
split; [ exact: (clt_ltT clt_02 ha) | exact: (clt_ltT clt_12 ha)  | exact: ha].
Qed.

Definition slist_good n m E :=
  [/\ slistp E, slength E = csucc(cmax n m) &
  forall i, i <c slength E ->  (Vg E i) = \1c \/ (Vg E i) = \3c ].





Lemma tree_value_injective t1 t2:
  treep t1 -> treep t2 ->
  (forall E, slist_good (tree_size t1) (tree_size t2) E ->
             tree_value E t1 = tree_value E t2) ->
  t1 =  t2.
Proof.
move => ha hb hc.
move: (Tree_to_tree_surjective ha) => [e ev].
move: (Tree_to_tree_surjective hb) => [e' ev'].
rewrite ev ev'; f_equal.
have: forall E, slist_good (nat_to_B (Tsize e)) (nat_to_B (Tsize e')) E ->
      Tree_value E e = Tree_value E e'.
  move => E; move: (hc E); rewrite ev ev'.
  move:(Tree_to_tree_prop e) =>[_ _ -> _].
  move:(Tree_to_tree_prop e') =>[_ _ -> _].
  rewrite !Tree_value_compat //.
clear.
have Ne1: nonempty \1c by exists \0c; apply:set1_1.
move:clt_3 => [lt03 /proj2 ne13 _].
have Ne3: nonempty \3c by exists \0c; apply/(NltP NS3). 
have H0 n n' f: let m := (nat_to_B n) in let m' :=  (nat_to_B n') in
   let k := csucc (cmax m m') in let E := Lg k f in
   (forall i, i <c  k -> (f i) = \1c \/ (f i) =\3c ) ->
    [/\ slist_good m m' E, Vg E m = f m & Vg E m' = f m']. 
  simpl.
  move: (nat_to_B_Nat n) (nat_to_B_Nat n').
  set m := nat_to_B n; set m' := nat_to_B n' => mN m'N fp.
  move: (Nmax_p1 mN m'N); set k := cmax _ _; move => [kN le1 le2].
  have skN := NS_succ kN.
  have lt1: m <c csucc k by apply/(cltSleP kN).
  have lt1': m' <c csucc k by apply/(cltSleP kN).
  have p3: inc m (csucc k) by apply/(NltP skN). 
  have p4: inc m' (csucc k) by apply/(NltP skN).
  have p5:slistp (Lg (csucc k) f) by split; aww.
  rewrite /slist_good /slength Lgd !LgV//; split => //; split => // i iln. 
  move/(NltP skN):(iln) => iin;  rewrite (LgV iin); exact: (fp _ iln).
have HA n t: (forall E, slist_good (nat_to_B n)
       (nat_to_B (Tsize (Tpowerset t))) E ->
      Tree_value E (Tbase n) = Tree_value E (Tpowerset t)) -> False.
   move => H.
   set k := csucc (cmax (nat_to_B n) (nat_to_B (Tsize t))). 
   have fp:(forall i, i <c k -> \3c = \1c \/ \3c = \3c) by move => _ _;right.
   move: (H0 n (Tsize (Tpowerset t)) _ fp) => [ra rb rc].
   by move:(H _ ra); rewrite /= rb => /not_a_powerset3.
have HB n t t': (forall E, slist_good (nat_to_B n)
    (nat_to_B (Tsize (Tproduct t t'))) E  ->
    Tree_value E (Tbase n) = Tree_value E (Tproduct t t')) -> False.
   move => H.
   set k:=csucc (cmax (nat_to_B n) (nat_to_B (maxn (Tsize t) (Tsize t')))).
   have fp:(forall i, i <c k -> \1c = \1c \/ \1c = \3c)  by move => _ _;left.
   move:(H0 n (Tsize (Tproduct t t')) _ fp) => [sa sb sc]. 
   by move: (H _ sa); rewrite /= sb => /not_a_product1.
have HC t t' t'' : (forall E, slist_good
    (nat_to_B (Tsize (Tpowerset t)))
    (nat_to_B (Tsize (Tproduct t' t''))) E ->
    Tree_value E (Tpowerset t) = Tree_value E (Tproduct t' t'')) -> False.
  set n := Tsize _; set n' := Tsize _ => H.
  set k := csucc (cmax (nat_to_B n) (nat_to_B n')).
  have fp:(forall i, i <c k -> \1c = \1c \/ \1c = \3c)   by move => _ _;left.
  by move:(H0 n n' _ fp) => [/H /powerset_not_product].
have He n m E x: (slist_good n m E) -> nat_to_B (Tsize x) <c slength E ->
       nonempty (Tree_value E x).
  move => ha hb; move:(Tree_to_tree_prop x) => [ra _ rb _]. 
  rewrite - rb in hb; rewrite - Tree_value_compat; apply: (tree_val_ne _ ra hb).
  by move => i ile; case: (proj33 ha _ ile) => ->.
have Hf T E E': 
    (forall i, i<=c (nat_to_B (Tsize T)) -> Vg E i = Vg E' i) ->
    Tree_value E T = Tree_value E' T.
  move => hi; rewrite - 2!Tree_value_compat.
  move:(Tree_to_tree_prop T) => [ra _ rb _]. 
  by apply: (tree_value_extent ra); rewrite rb.
pose ext E a b := Lg (csucc (cmax a b)) 
    (fun z => Yo (z <c (slength E)) (Vg E z) \1c).
have ext_p1 n m a b E: let E' :=  (ext E a b) in 
    slist_good n m E -> natp a -> natp b -> slength E <=c csucc(cmax a b) ->
    [/\ slist_good a b E', a <c slength E',  b <c slength E' &
     forall i, i <c (slength E) -> Vg E i = Vg E' i].
  move => E' [ha hb hc] aN bN hd.
  move:(Nmax_p1 aN bN) => [ma mb mc].
  set k := (csucc (cmax a b)).
  have le: slength (ext E a b) = k by rewrite /slength /ext; aw.
  have sa1: a <c slength (ext E a b) by rewrite le; apply/(cltSleP ma).
  have sb1: b <c slength (ext E a b) by rewrite le; apply/(cltSleP ma).
  have lex: slistp (ext E a b) by rewrite /slistp/ext; aw; split;fprops.
  have he:slist_good a b (ext E a b).
    split => //. rewrite le => i il.
    have ii:inc i k by apply /(NltP (NS_succ ma)).
    rewrite /ext LgV//; Ytac hi;[ by apply:hc | by left ].
  split => // i il.
  have ii:inc i (slength E) by apply /(NltP (proj2  ha)).
  have ii2:inc i k by apply /(NltP (NS_succ ma)); exact:(clt_leT il hd). 
  by rewrite /E'/ext LgV//; Ytac0; done.

have mc  n m: cmax (nat_to_B n) (nat_to_B m) = cmax (nat_to_B m) (nat_to_B n). 
 by rewrite  - ! nat_to_B_max maxnC.

elim: e e'.
- move => n e. 
  case:e.
  + move => n' H.
    set m := (nat_to_B n).
    case: (equal_or_not (nat_to_B n') m) => mm.
      by rewrite (nat_to_B_injective mm).
    set k := csucc (cmax (nat_to_B n) (nat_to_B n')).
    have hf:(forall i,
     i <c k -> variant m \1c \3c i = \1c \/ variant m \1c \3c i = \3c).
      by move => i _; rewrite/variant; Ytac w; [left | right].
    move: (H0 n n' _ hf) => [/H sa sb sc].
    move: sa; rewrite /= sb sc.
    by rewrite (variant_true _ _ (erefl _ )) (variant_false _ _ mm) => /ne13.
  + move => t h; case: (HA n t h).
  + move => t t' h; case: (HB n t t' h).
- move => t h; case.
  + move => n /= h1; case: (HA n t) => E [ ea eb ec];  rewrite /= h1 //.
    by move: eb; rewrite /= mc => eb. 
  + move => t' /= ha; rewrite (h t') // => E  ev.
    exact:(powerset_injective (ha _ ev)).
  + move => t' t'' h1; case:(HC _ _ _ h1).
- move => t ht t' ht'; case.
  + move => n H; case: (HB n t t') => E [ea eb ec].
    by rewrite mc in eb; rewrite H.
  + move => t'' h; case: (HC t'' t t') => E [ea eb ec].
    by rewrite mc in eb; rewrite h.
  + move => t2 t3 /=.
    set l1 := maxn _ _; set l2 := maxn _ _; set l3 := maxn l1 l2 => h.
    move: (nat_to_B_Nat l1)(nat_to_B_Nat l2) => l1N l2N.
    have ->: t = t2.
      apply: ht => E ep.
      move: (ep) => [p0 p1 p2].
      have se: slength E <=c csucc (cmax (nat_to_B l1) (nat_to_B l2)).
        rewrite p1; apply /cleSS; rewrite /l1 /l2 - 2!nat_to_B_max maxnACA. 
        by apply/nat_to_B_le; apply: leq_maxl.
      have se2: nat_to_B (Tsize t) <c slength E.
        rewrite p1 -nat_to_B_max nat_to_B_succ;  apply/nat_to_B_lt.
        by rewrite ltnS leq_maxl.
      have se3: nat_to_B (Tsize t2) <c slength E.
        rewrite p1 -nat_to_B_max nat_to_B_succ;  apply/nat_to_B_lt.
        by rewrite ltnS leq_maxr.
      move: (ext_p1 _ _ _ _ _ ep l1N l2N se).
      set E' := ext _ _ _; move => [sa sb sc sd].
      have pa:forall i, i <=c nat_to_B (Tsize t) -> Vg E i = Vg E' i.
        by move => i lin; apply: sd; exact:(cle_ltT lin se2).
      have pb:forall i, i <=c nat_to_B (Tsize t2) -> Vg E i = Vg E' i.
        move => i lin; apply: sd; exact:(cle_ltT lin se3).
     move: (product_injective (He _ _ _ (Tproduct t2 t3) sa sc) (h _ sa)).
     by rewrite -/(Tree_value _) (Hf t E E' pa)  (Hf t2 E E' pb); case.
   have -> //: t' = t3.
   apply: ht' => E ep.
   move: (ep) => [p0 p1 p2].
   have se: slength E <=c csucc (cmax (nat_to_B l1) (nat_to_B l2)).
     rewrite p1; apply /cleSS; rewrite /l1 /l2 - 2!nat_to_B_max maxnACA. 
     by apply/nat_to_B_le; apply: leq_maxr.
   have se2: nat_to_B (Tsize t') <c slength E.
      rewrite p1 -nat_to_B_max nat_to_B_succ;  apply/nat_to_B_lt.
      by rewrite ltnS leq_maxl.
   have se3: nat_to_B (Tsize t3) <c slength E.
     rewrite p1 -nat_to_B_max nat_to_B_succ;  apply/nat_to_B_lt.
     by rewrite ltnS leq_maxr.
   move: (ext_p1 _ _ _ _ _ ep l1N l2N se).
   set E' := ext _ _ _; move => [sa sb sc sd].
   have pa:forall i, i <=c nat_to_B (Tsize t') -> Vg E i = Vg E' i.
      by move => i lin; apply: sd; move:(cle_ltT lin se2).
   have pb:forall i, i <=c nat_to_B (Tsize t3) -> Vg E i = Vg E' i.
      by move => i lin; apply: sd; move:(cle_ltT lin se3).
  move: (product_injective  (He _ _ _ (Tproduct t2 t3) sa sc)  (h _ sa)).
  by rewrite -/(Tree_value _) (Hf t' E E' pa)(Hf t3 E E' pb); case.
Qed.


Lemma tree_value_commutes E c (f := echelon_value c E)
      (t :=echelon_to_trees c)
      (g := Lg (domain c) (fun i => (tree_value E (Vg t i)))):
   echelon c -> f = g.
Proof.
move => ec; symmetry.
have mN:= (proj2(proj1(proj1 ec))).
move:(echelon_to_trees_prop ec); rewrite -/t; move => [ta tb tc td].
have ha: domain g = slength c by rewrite /g; aw.
have ndg: natp (domain g) by rewrite ha.
have hb: slistpl g (slength c) by split => //; split => //; rewrite /g; fprops.

apply: (erecdef_unique1 ec hb).
move => i il; move:(td _ il) => /= [ua ub uc].
have idc: inc i (domain c) by apply/(NltP mN).
have iN:= (NS_lt_nat il mN).
split.
- move => w; move:(ua w) =>[sa sb sc]; rewrite /g LgV// sc.
  rewrite (proj31 (tree_value_prop E)) //.
  exact:  (proj31(cpred_pr6' (NS_esize ec) sa sb)).
- move => w; move: (ub w) => [sa sb sc]. 
  move:(cpred_pr6' iN sa sb)=> [pa pb pc].
  have lt2:= (clt_ltT pc il).
  have cpd: inc (cpred (P (Vg c i))) (domain c) by apply/(NltP mN).
  rewrite /g /Vl LgV// LgV// sc// (proj32 (tree_value_prop E)) //.
  by apply: tc.
- move => w1 w2;move: (uc w1 w2) => [sa sb sa' sb' sc].
  move:(cpred_pr6' iN sa sb)=> [pa pb pc].
  move:(cpred_pr6' iN sa' sb')=> [pa' pb' pc'].
  have lt2:= (clt_ltT pc il).
  have cpd: inc (cpred (P (Vg c i))) (domain c) by apply/(NltP mN).
  have lt2':= (clt_ltT pc' il).
  have cpd': inc (cpred (Q (Vg c i))) (domain c) by apply/(NltP mN).
  rewrite /g /Vl LgV// LgV// LgV//.
  by rewrite sc// (proj33 (tree_value_prop E) _ _ (tc _ lt2) (tc _ lt2')).
Qed.

Definition echelon_to_tree c := Vl (echelon_to_trees c) (slength c).

Lemma tree_value_commmute_bis E c1 c2: 
  echelon c1 -> echelon c2 -> \0c <c slength c1 -> \0c <c slength c2 -> 
  echelon_to_tree c1 = echelon_to_tree c2 ->
  echelon_of_base c1 E = echelon_of_base c2 E.
Proof.
move => ha hb z1 z2.
have i1: inc (cpred (slength c1)) (domain c1).
  move: (proj2 (proj1 (proj1 ha))) => lN.
  apply/(NltP lN); exact:(cpred_lt lN (nesym (proj2 z1))).
have i2: inc (cpred (slength c2)) (domain c2).
  move: (proj2 (proj1 (proj1 hb))) => lN.
  apply/(NltP lN); exact:(cpred_lt lN (nesym (proj2 z2))).
move: (tree_value_commutes E ha).
move: (tree_value_commutes E hb).
rewrite /echelon_of_base /echelon_to_tree /Vl.
by move => -> ->; rewrite !LgV//; move => -> //.
Qed.



(* Example *)

Lemma cpred2: cpred \2c = \1c.
Proof. by rewrite - succ_one (cpred_pr1 CS1). Qed.

Lemma cpred3: cpred \3c = \2c.
Proof. by rewrite (cpred_pr1 (CS_nat NS2)). Qed.

Lemma cpred4: cpred \4c = \3c.
Proof. by rewrite (cpred_pr1 (CS_nat NS3)). Qed.

Lemma cpred5: cpred \5c = \4c.
Proof. by rewrite (cpred_pr1 (CS_nat NS4)). Qed.

Lemma cpred6: cpred \6c = \5c.
Proof. by rewrite (cpred_pr1 (CS_nat NS5)). Qed.


Lemma clt_4: [/\ \0c <c \4c, \1c <c \4c, \2c <c \4c & \3c <c \4c]. 
Proof.
by have hd:=(cltS NS3);move:clt_3 => [ha hb hc]; split => //; apply: clt_ltT hd.
Qed.


Lemma clt_5: [/\ \0c <c \5c, \1c <c \5c, \2c <c \5c, \3c <c \5c & \4c <c \5c ]. 
Proof.
have he:=(cltS NS4);move:clt_4 => [ha hb hc hd].
by split => //; apply: clt_ltT he.
Qed.


Lemma clt_6: [/\ \0c <c \6c, \1c <c \6c, \2c <c \6c, \3c <c \6c &
                                       \4c <c \6c /\  \5c <c \6c]. 
Proof.
have hf:=(cltS NS5);move:clt_5 => [ha hb hc hd he].
move: (clt_ltT ha hf) (clt_ltT hb hf) (clt_ltT hc hf) => ra rb rc.
move: (clt_ltT hd hf) (conj (clt_ltT he hf) hf)=> rd re.
done.
Qed.

Definition  slist1 a:= Lg \1c (fun z => a).


Lemma slist1_prop a (s := slist1 a):
  slistpl s \1c /\ Vg s \0c = a.
Proof.
have i01 := set1_1 \0c.
have h: slistp (Lg \1c (fun _ : Set => a)) by split; aw;fprops.
by rewrite/s/slistpl/slist1 /slength Lgd  !LgV.
Qed.


Definition slist2 a b := Lg \2c (fun z => Yo (z = \0c) a b).

Lemma slist2_prop a b (c:= slist2 a b):
  [/\ slistpl c \2c, Vg c \0c = a & Vg c \1c = b].
Proof.
have fgE: fgraph c by apply: Lg_fgraph. 
have dE: domain c = \2c by exact: Lgd.
have le: slistp c by split; [ exact | rewrite dE; exact NS2 ].
have sa:inc \1c \2c by apply /(NltP NS2); exact: clt_12.
have sb:inc \0c \2c by apply /(NltP NS2); exact: clt_02.
have sc:=card1_nz.
by split => //;rewrite ?(LgV sa) ?(LgV sb); Ytac0.  
Qed.



Definition slist6 a b c d e f:= 
  Lg \6c (fun z => Yo (z = \0c) a (Yo (z = \1c) b
       (Yo (z = \2c) c (Yo (z = \3c) d (Yo (z = \4c) e f))))).

Lemma slist6_prop a b c d e f (E:= slist6 a b c d e f):
  [/\ slistpl E \6c, Vg E \0c = a, Vg E \1c = b &
   [/\ Vg E \2c = c, Vg E \3c = d , Vg E \4c = e & Vg E \5c = f ]].
Proof.
move: NS0 NS1 NS2 NS3 NS4 NS5 NS6 => ns0 ns1 ns2 ns3 ns4 ns5 ns6.
have fgE: fgraph E by apply: Lg_fgraph.
have dE: domain E = \6c by exact: Lgd.
have lE: slistp E by split => //; rewrite dE.
move:(clt_6) => [l06 l16 l26 l36 [l46 l56]].
have i06: inc \0c \6c by apply/(NltP ns6).
have i16: inc \1c \6c by apply/(NltP ns6).
have i26: inc \2c \6c by apply/(NltP ns6).
have i36: inc \3c \6c by apply/(NltP ns6).
have i46: inc \4c \6c by apply/(NltP ns6).
have i56: inc \5c \6c by apply/(NltP ns6).
split => //.
-  by rewrite (LgV i06); Ytac0.
-  by rewrite (LgV i16) (Y_false(nesym (proj2 clt_01))); Ytac0.
- split.
- rewrite (LgV i26) (Y_false(nesym (proj2 clt_02))).
  by rewrite  (Y_false(nesym (proj2 clt_12))); Ytac0.
-  move:clt_3 => [lt03 lt13 lt23].
   rewrite (LgV i36) (Y_false(nesym (proj2 lt03))).
   rewrite  (Y_false(nesym (proj2 lt13))).
   by rewrite  (Y_false(nesym (proj2 lt23))); Ytac0.
-  move:clt_4 => [lt04 lt14 lt24 lt34].
   rewrite (LgV i46) (Y_false(nesym (proj2 lt04))).
   rewrite  (Y_false(nesym (proj2 lt14))).
   rewrite  (Y_false(nesym (proj2 lt24))).
   by rewrite  (Y_false(nesym (proj2 lt34))); Ytac0.
- move:clt_5 => [lt05 lt15 lt25 lt35 lt45].
   rewrite (LgV i56) (Y_false(nesym (proj2 lt05))).
   rewrite  (Y_false(nesym (proj2 lt15))).
   rewrite  (Y_false(nesym (proj2 lt25))).
   rewrite  (Y_false(nesym (proj2 lt35))).
   by rewrite  (Y_false(nesym (proj2 lt45))).
Qed.

Definition scheme_ex1 := slist6 (J \0c \1c) (J \0c \2c) (J \1c \0c)
                          (J \3c \0c) (J \2c \0c) (J \4c \5c).
Definition scheme_ex2 := slist6 (J \0c \2c) (J \0c \1c) (J \1c \0c)
                          (J \2c \0c) (J \4c \0c) (J \5c \3c).

Lemma scheme_ex1_ok1 (E := scheme_ex1):
 [/\ echelon E, slength E = \6c, esize E = \2c
  & [/\ Vg E \0c = J \0c \1c, Vg E \1c = J \0c \2c, Vg E \2c = J \1c \0c,
      Vg E \3c = J \3c \0c&  (Vg E \4c =J \2c \0c /\  Vg E \5c =J \4c \5c) ]].

Proof.
move: NS0 NS1 NS2 NS3 NS4 NS5 NS6 => ns0 ns1 ns2 ns3 ns4 ns5 ns6.
move: (slist6_prop  (J \0c \1c) (J \0c \2c) (J \1c \0c)
                          (J \3c \0c) (J \2c \0c) (J \4c \5c)).
rewrite /= -/ scheme_ex1 -/E.
move => [[ha sE] E0 E1 [E2 E3 E4 E5]].
have rE:slist_E E (Nat \times Nat).
  split; first exact.
  move => i /Lg_range_P [b bN ->]; Ytac h1;first by apply:setXp_i. 
  Ytac h2; first by apply:setXp_i. 
  Ytac h3; first by apply:setXp_i. 
  Ytac h4; first by apply:setXp_i. 
  by Ytac h5;  apply:setXp_i. 
move:clt_5 => [lt05 lt15 lt25 lt35 lt45].
move:clt_4 => [lt04 lt14 lt24 lt34].
move:clt_3 => [lt03 lt13 lt23].
move: (proj1 clt_12) => cle_12.
have EE: echelon E.
  split => //; rewrite sE => i /(cltSleP ns5) /cle_eqVlt;case.
    move:  (proj1 lt14) (proj1 lt45) (proj1 lt15) => ua ub uc.
    have ra: ech_good \4c \5c by split.
    have rb: ech_good \5c \5c by split; fprops.
    by move => ->; rewrite E5; simpl; aw.
  move /(cltSleP ns4) /cle_eqVlt;case.
    have hb:=(proj1 lt24).
    by move => ->; rewrite E4 /=; aw; split.
  move /(cltSleP ns3) /cle_eqVlt;case.
    move => ->; rewrite E3 /=; saw; last by case.
    split; [ exact: (proj1 lt13) | fprops].
  move /(cltSleP ns2) /cle_eqVlt;case.
    move => ->; rewrite E2 /=; aw ; split => //  _; split; fprops.
  case /clt2 => ->.
     by move: (card1_nz) => ra; rewrite E0 /=; saw.
  by move: (card2_nz) => ra; rewrite E1 /=; saw.
split => //.
move:(clt_6) => [l06 l16 l26 l36 [l46 l56]].
have sp: \0c <c slength E by rewrite sE.
move: (esize_prop1 EE sp); set n := esize E.
move => [ra rb rc rd].
apply: cleA; last first.
  have ww: \1c <c slength E  by ue.
  by move: (rd _ ww); rewrite E1; aw; apply.
move: rc =>[j]; rewrite sE;move /(cltSleP ns5) /cle_eqVlt;case.
  move ->; rewrite E5 => /(f_equal P); aw => e40.
  by case:(proj2 lt04).
move /(cltSleP ns4) /cle_eqVlt;case.
  by move => ->; rewrite E4 => /(f_equal P); aw => z2; case: (card2_nz).
move /(cltSleP ns3) /cle_eqVlt;case.
  move => ->; rewrite E3 => /(f_equal P); aw => z3.
  by case:(proj2 lt03). 
move /(cltSleP ns2) /cle_eqVlt;case.
  by move => ->; rewrite E2  => /(f_equal P); aw => z3;  case: card1_nz.
case /clt2 => ->; rewrite ?E0 ? E1; move /(f_equal Q); aw => <-; fprops.
Qed.

Lemma scheme_ex2_ok1 (E := scheme_ex2):
 [/\ echelon E, slength E = \6c, esize E = \2c
  & [/\ Vg E \0c = J \0c \2c, Vg E \1c = J \0c \1c, Vg E \2c = J \1c \0c,
      Vg E \3c = J \2c \0c&  (Vg E \4c =J \4c \0c /\  Vg E \5c =J \5c \3c) ]].

Proof.
move: NS0 NS1 NS2 NS3 NS4 NS5 NS6 => ns0 ns1 ns2 ns3 ns4 ns5 ns6.
move: (slist6_prop  (J \0c \2c) (J \0c \1c) (J \1c \0c)
                          (J \2c \0c) (J \4c \0c) (J \5c \3c)).

rewrite /= -/ scheme_ex2 -/E.
move => [[ha sE] E0 E1 [E2 E3 E4 E5]].
have rE:slist_E E (Nat \times Nat).
  split; first exact.
  move => i /Lg_range_P [b bN ->]; Ytac h1;first by apply:setXp_i. 
  Ytac h2; first by apply:setXp_i. 
  Ytac h3; first by apply:setXp_i. 
  Ytac h4; first by apply:setXp_i. 
  by Ytac h5;  apply:setXp_i. 
move:clt_5 => [lt05 lt15 lt25 lt35 lt45].
move:clt_4 => [lt04 lt14 lt24 lt34].
move:clt_3 => [lt03 lt13 lt23].
move: (proj1 clt_12) => cle_12.
have EE: echelon E.
  split => //; rewrite sE => i /(cltSleP ns5) /cle_eqVlt;case.
  move:  (proj1 lt13) (proj1 lt35) (proj1 lt15) => ua ub uc.
    have ra:ech_good \3c \5c by split.
    have rb: ech_good \5c \5c by split; fprops.
    by move => ->; rewrite E5; simpl; aw.
  move /(cltSleP ns4) /cle_eqVlt;case.
  move => ->; rewrite E4 /=; aw; split => // _.
    split; [ exact: (proj1 lt14) | fprops].
  move /(cltSleP ns3) /cle_eqVlt;case.
    move => ->; rewrite E3 /=; aw; split => //_.
    split; [ exact | exact: (proj1 lt23)].
  move /(cltSleP ns2) /cle_eqVlt;case.
    move => ->; rewrite E2 /=; aw ; split => //_; split; fprops.
  case /clt2 => ->. 
     by move: (card2_nz) => ra; rewrite E0 /=; aw; split.
  by move: (card1_nz) => ra; rewrite E1 /=; aw; split.
split => //.
move:(clt_6) => [l06 l16 l26 l36 [l46 l56]].
have sp: \0c <c slength E by rewrite sE.
move: (esize_prop1 EE sp); set n := esize E.
move => [ra rb rc rd].
apply: cleA; last first.
  have ww: \0c <c slength E  by ue.
  by move: (rd _ ww); rewrite E0; aw; apply.
move: rc =>[j]; rewrite sE;move /(cltSleP ns5) /cle_eqVlt;case.
  move ->; rewrite E5 => /(f_equal P); aw => e50.
  by case:(proj2 lt05).
move /(cltSleP ns4) /cle_eqVlt;case.
  move => ->; rewrite E4 => /(f_equal P); aw => e40.
  by case:(proj2 lt04).
move /(cltSleP ns3) /cle_eqVlt;case.
  by move => ->; rewrite E3 => /(f_equal P); aw => /card2_nz.
move /(cltSleP ns2) /cle_eqVlt;case.
  by move => ->; rewrite E2  => /(f_equal P); aw => z3;  case: card1_nz.
case /clt2 => ->; rewrite ?E0 ? E1; move /(f_equal Q); aw => <-; fprops.
Qed.


Definition Tree6 := echelon_to_trees scheme_ex1.
Definition Tree6' := echelon_to_trees scheme_ex2.

Lemma tree6_1: [/\
     Vg Tree6 \0c = Tree_to_tree (Tbase 0),
     Vg Tree6 \1c = Tree_to_tree (Tbase 1),
     Vg Tree6 \2c = Tree_to_tree (Tpowerset (Tbase 0)),
     Vg Tree6 \3c = Tree_to_tree (Tpowerset (Tpowerset (Tbase 0))) &
    Vg Tree6 \4c = Tree_to_tree (Tpowerset (Tbase 1)) /\
    Vg Tree6 \5c =
       Tree_to_tree
         (Tproduct (Tpowerset (Tpowerset (Tbase 0))) (Tpowerset (Tbase 1)))].
Proof.
move: scheme_ex1_ok1 => [ha hb hc [v0 v1 v2 v3 [v4 v5]]].
move:(clt_6) => [lt06 lt16 lt26 lt36 [lt46 lt56]].
have V0: (Vg Tree6 \0c) = Tree_to_tree (Tbase 0).
  have ra: \0c <c slength (scheme_ex1) by rewrite hb.
  move: (ET_val1 ha ra); rewrite v0; aw => zz; move: (zz (erefl \0c)).
  move => [n [na ->]].
  have: nat_to_B 1 = nat_to_B n.+1 by rewrite /= succ_zero na.
  move/nat_to_B_injective => /eqP; rewrite eqSS => /eqP <- //.
have V1: Vg Tree6 \1c = Tree_to_tree (Tbase 1).
  have ra: \1c <c slength (scheme_ex1) by rewrite hb; exact:lt16.
  move: (ET_val1 ha ra); rewrite v1; aw => zz; move: (zz (erefl \0c)).
  move => [n [na ->]].
  have: nat_to_B 2 = nat_to_B n.+1 by rewrite /= succ_zero succ_one na.
  by move/nat_to_B_injective => /eqP; rewrite eqSS => /eqP <-.
have V2: (Vg Tree6 \2c) = Tree_to_tree (Tpowerset (Tbase 0)).
  have ra: \2c <c slength (scheme_ex1) by rewrite hb.
  move: (ET_val2 ha ra); rewrite v2; aw => zz; move: (zz (erefl \0c)).
  by move => [E]; rewrite /Vl cpred1 V0 => /Tree_to_tree_injective ->.
have V3: (Vg Tree6 \3c) = Tree_to_tree (Tpowerset (Tpowerset (Tbase 0))).
  have ra: \3c <c slength (scheme_ex1) by rewrite hb.
  move: (ET_val2 ha ra); rewrite v3; aw => zz; move: (zz (erefl \0c)).
  move => [E ]; rewrite /Vl.
  by rewrite -/Tree6 /Vl cpred3 V2 => /Tree_to_tree_injective ->.
have V4: (Vg Tree6 \4c) = Tree_to_tree (Tpowerset (Tbase 1)).
  have ra: \4c <c slength (scheme_ex1) by rewrite hb.
  move: (ET_val2 ha ra); rewrite v4; aw => zz; move: (zz (erefl \0c)).
  by move => [E]; rewrite /Vl cpred2 V1  => /Tree_to_tree_injective ->.
have V5: (Vg Tree6 \5c) = 
  Tree_to_tree (Tproduct(Tpowerset(Tpowerset (Tbase 0))) (Tpowerset (Tbase 1))).
  have ra: \5c <c slength (scheme_ex1) by rewrite hb.
  move: (ET_val3 ha ra); rewrite v5; aw => zz.
  move: (zz (@succ_nz \3c) (@succ_nz \4c)).
  rewrite -/Tree6 /Vl cpred4 cpred5 V3 V4; move=> [E [F []]].
  move=> /Tree_to_tree_injective -> /Tree_to_tree_injective -> //.
done.
Qed.


Lemma  tree6_2:  echelon_to_tree scheme_ex1 = echelon_to_tree scheme_ex2.
Proof.
move: scheme_ex2_ok1 => [ha hb hc [v0 v1 v2 v3 [v4 v5]]].
move: scheme_ex1_ok1 => [_ hb' _ _].
suff: (Vg Tree6' \5c) =  (Vg Tree6 \5c).
 by rewrite /echelon_to_tree /Vl hb hb' (cpred_pr1 (CS_nat NS5)).
move: tree6_1 => [_ _ _ _ [ _ ->]].
move:(clt_6) => [lt06 lt16 lt26 lt36 [lt46 lt56]].
have V0: (Vg Tree6' \0c) = Tree_to_tree (Tbase 1).
  have ra: \0c <c slength (scheme_ex2) by rewrite hb.
  move: (ET_val1 ha ra); rewrite v0; aw => zz; move: (zz (erefl \0c)).
  move => [n [na ->]].
  have: nat_to_B 2 = nat_to_B n.+1 by rewrite /= succ_zero succ_one na.
  by move/nat_to_B_injective => /eqP; rewrite eqSS => /eqP <- //.
have V1: (Vg Tree6' \1c) = Tree_to_tree (Tbase 0).
  have ra: \1c <c slength (scheme_ex2) by rewrite hb.
  move: (ET_val1 ha ra); rewrite v1; aw => zz; move: (zz (erefl \0c)).
  move => [n [na ->]].
  have: nat_to_B 1 = nat_to_B n.+1 by rewrite /= succ_zero na.
  by move/nat_to_B_injective => /eqP; rewrite eqSS => /eqP <- //.
have V2: (Vg Tree6' \2c) = Tree_to_tree (Tpowerset (Tbase 1)).
  have ra: \2c <c slength (scheme_ex2) by rewrite hb.
  move: (ET_val2 ha ra); rewrite v2; aw => zz; move: (zz (erefl \0c)).
  by move => [E]; rewrite /Vl cpred1 V0 => /Tree_to_tree_injective ->.
have V3: (Vg Tree6' \3c) = Tree_to_tree (Tpowerset (Tbase 0)).
  have ra: \3c <c slength (scheme_ex2) by rewrite hb.
  move: (ET_val2 ha ra); rewrite v3; aw => zz; move: (zz (erefl \0c)).
  move => [E ]; rewrite /Vl.
  by rewrite -/Tree6 /Vl cpred2 V1 => /Tree_to_tree_injective ->.
have V4: (Vg Tree6' \4c) = Tree_to_tree (Tpowerset (Tpowerset (Tbase 0))).
  have ww: (cpred \4c) = \3c by rewrite (cpred_pr1 (CS_nat NS3)).
  have ra: \4c <c slength (scheme_ex2) by rewrite hb.
  move: (ET_val2 ha ra); rewrite v4; aw => zz; move: (zz (erefl \0c)).
  by  move => [E]; rewrite /Vl ww V3  => /Tree_to_tree_injective ->.

  have ra: \5c <c slength (scheme_ex2) by rewrite hb.
  move: (ET_val3 ha ra); rewrite v5; aw => zz.
  move: (zz (@succ_nz \4c) (@succ_nz \2c)).
  rewrite -/Tree6 /Vl cpred3 cpred5 V2 V4; move=> [E [F []]].
  move=> /Tree_to_tree_injective -> /Tree_to_tree_injective -> //.
Qed.
  

(* -- *)
  
Definition scheme_val1 U V:=
  slist6 U V  (\Po U) (\Po(\Po U)) (\Po V)
   ((\Po(\Po U)) \times (\Po V)).

Lemma echelon_ex1_value U V: 
   echelon_value scheme_ex1 (slist2 U V) = scheme_val1 U V.
Proof.
move: scheme_ex1_ok1=> [sa sb sc [E0 E1 E2 E3 [E4 E5]]].
move:(slist2_prop U V) => [[ra rb] rU rV].
move: (slist6_prop U V  (\Po U) (\Po(\Po U)) (\Po V)
   ((\Po(\Po U)) \times (\Po V))).
rewrite /= -/(scheme_val1 U V); set F := (scheme_val1 U V).
move => [[Fl Fs] F0 F1 [F2 F3 F4 F5]].
have ss: slength F = slength scheme_ex1 by rewrite Fs sb.
symmetry;apply: (erecdef_unique1 sa (conj Fl ss)).
move: (@succ_nz \2c) (@succ_nz \3c) (@succ_nz \4c) => aa ab ac.
have ad:= card2_nz.
have ae:= card1_nz.
have cp1: (cpred \1c) = \0c by rewrite cpred1.
have cp2: (cpred \2c) = \1c by rewrite -(cpred_pr2 NS1) succ_one.
have cp3: (cpred \3c) = \2c by apply: (cpred_pr2 NS2).
have cp4: (cpred \4c) = \3c by apply: (cpred_pr2 NS3).
have cp5: (cpred \5c) = \4c by apply: (cpred_pr2 NS4).
rewrite sb => i /(cltSleP NS5) /cle_eqVlt;case.
  move => -> /=; rewrite E5 F5; aw.
  by split => //; rewrite /Vl cp4 cp5 F3 F4.
move /(cltSleP NS4) /cle_eqVlt;case.
  move => -> /=; rewrite E4; aw; split => //.
  by rewrite /Vl cp2 F4 F1.
move /(cltSleP NS3) /cle_eqVlt;case.
  move => -> /=; rewrite E3; aw; split => //.
  by rewrite /Vl cp3 F3 F2.
move /(cltSleP NS2) /cle_eqVlt;case.
  move: card1_nz => z1;move => -> /=; rewrite E2; aw; split => //.
  by rewrite /Vl cp1 F2 F0.
case /clt2 => -> /=. 
  by rewrite E0; aw; split => //; rewrite F0 /Vl cp1 rU.
by rewrite E1; aw; split => //; rewrite F1 /Vl cp2 rV.
Qed.

Lemma echelon_of_base_ex1 U V:
  echelon_of_base scheme_ex1 (slist2 U V) =
  ((\Po(\Po U)) \times (\Po V)).
Proof.
rewrite /echelon_of_base (echelon_ex1_value U V).
move: scheme_ex1_ok1 => [ha hb hc _].
rewrite hb /Vl (cpred_pr2 NS5).
move: (slist6_prop U V  (\Po U) (\Po(\Po U)) (\Po V)
   ((\Po(\Po U)) \times (\Po V))) => [ _ _ _ [_ _ _]].
done.
Qed.  


(** Canonical extensions *)

Definition echelon_extension c f :=
  echelon_recdef (Vl f) extension_to_parts ext_to_prod c.


Definition echelon_can_extension c f := 
  Vl (echelon_extension c f) (slength c).


Lemma echelon_can_extensionE c f:
  echelon_can_extension c f =
  echelon_recdef_last  (Vl f) extension_to_parts ext_to_prod c.
Proof. by []. Qed.


Lemma Eextension_prop c f i (m := slength c)(g :=  echelon_extension c f)
   (n:=  esize c):
  echelon c -> i <c m ->
  let a:= P (Vg c i) in let b := Q (Vg c i) in
  [/\ a = \0c -> [/\ \1c <=c b, b <=c n & Vg g i = (Vl f b)],
      b = \0c -> [/\ \1c <=c a, a <=c i & 
          Vg g i = \Pof (Vl g a) ]
    & a <> \0c -> b <> \0c -> [/\ \1c <=c a, a <=c i, \1c <=c b, b <=c i &
   Vg g i = (Vl g a) \ftimes (Vl g b)]].
Proof. by move => h; apply:erecdef_prop2. Qed.

Definition tree_extension f x := tree_rec
  (fun n => Vg f n)
  (fun t => extension_to_parts t)
  (fun t t'  => ext_to_prod t t') x.

Lemma tree_extension_prop f:
  [/\ (forall n, natp n -> tree_extension f (Tb n) = Vg f n),
     (forall x, treep x -> tree_extension f (Tp x) = 
        \Pof (tree_extension f x))&
     (forall x y, treep x -> treep y -> 
        tree_extension f (Tx x y) =
         (tree_extension f x) \ftimes (tree_extension f y))].
Proof.
rewrite /tree_extension;split.
- by move => n nN; rewrite tree_recdef_pb'.
- by move => t tp ; rewrite  tree_recdef_pp.
- by move => t t' tp tp' ; rewrite  tree_recdef_px.
Qed.



Lemma tree_extension_commutes f c 
      (t :=echelon_to_trees c)
      (g := Lg (domain c) (fun i => (tree_extension f (Vg t i)))):
   echelon c -> (echelon_extension c f)  = g.
Proof.
move => ec; symmetry.
have mN:= (proj2(proj1(proj1 ec))).
move:(echelon_to_trees_prop ec); rewrite -/t; move => [ta tb tc td].
have ha: domain g = slength c by rewrite /g; aw.
have ndg: natp (domain g) by rewrite ha.
have hb: slistpl g (slength c) by split => //; split => //; rewrite /g; fprops.
apply: (erecdef_unique1 ec hb).

move => i il; move:(td _ il) => /= [ua ub uc].
have idc: inc i (domain c) by apply/(NltP mN).
have iN:= (NS_lt_nat il mN).
split.
- move => w; move:(ua w) =>[sa sb sc]; rewrite /g LgV// sc.
  rewrite (proj31 (tree_extension_prop f)) //.
  exact:  (proj31(cpred_pr6' (NS_esize ec) sa sb)).
- move => w; move: (ub w) => [sa sb sc]. 
  move:(cpred_pr6' iN sa sb)=> [pa pb pc].
  have lt2:= (clt_ltT pc il).
  have cpd: inc (cpred (P (Vg c i))) (domain c) by apply/(NltP mN).
  rewrite /g /Vl LgV// LgV// sc// (proj32 (tree_extension_prop f)) //.
  by apply: tc.
- move => w1 w2;move: (uc w1 w2) => [sa sb sa' sb' sc].
  move:(cpred_pr6' iN sa sb)=> [pa pb pc].
  move:(cpred_pr6' iN sa' sb')=> [pa' pb' pc'].
  have lt2:= (clt_ltT pc il).
  have cpd: inc (cpred (P (Vg c i))) (domain c) by apply/(NltP mN).
  have lt2':= (clt_ltT pc' il).
  have cpd': inc (cpred (Q (Vg c i))) (domain c) by apply/(NltP mN).
  rewrite /g /Vl LgV // LgV// LgV//.
  by rewrite sc// (proj33 (tree_extension_prop f) _ _ (tc _ lt2) (tc _ lt2')).
Qed.

Lemma tree_extension_commmute_bis E c1 c2: 
  echelon c1 -> echelon c2 -> \0c <c slength c1 -> \0c <c slength c2 -> 
  echelon_to_tree c1 = echelon_to_tree c2 ->
  echelon_can_extension c1 E = echelon_can_extension c2 E.
Proof.
move => ha hb z1 z2.
have i1: inc (cpred (slength c1)) (domain c1).
  move: (proj2 (proj1 (proj1 ha))) => lN.
  apply/(NltP lN); exact:(cpred_lt lN (nesym (proj2 z1))).
have i2: inc (cpred (slength c2)) (domain c2).
  move: (proj2 (proj1 (proj1 hb))) => lN.
  apply/(NltP lN); exact:(cpred_lt lN (nesym (proj2 z2))).
move: (tree_extension_commutes E ha).
move: (tree_extension_commutes E hb).
rewrite /echelon_can_extension /echelon_to_tree /Vl.
by move => -> ->; rewrite !LgV//; move => -> //.
Qed.

Lemma can_extension_of_tree t E: treep t ->
   echelon_can_extension (tree_to_echelon t) E = tree_extension E t.
Proof.
move:(tree_extension_prop E) => [ha hb hc].
move: tree_to_echelon_E => [qa qb qc].
move: t;apply: tree_ind.
- move => n nN.
  move:(NS_succ nN) (succ_positive n) => hu hv.
  rewrite (ha _ nN) (qa _ nN) echelon_can_extensionE erecdef_base // /Vl. 
  by rewrite (cpred_pr1 (CS_nat nN)).
- move => x tx Hr.
  move:(tree_to_echelon_ok tx) => [sa sb sc].
    by rewrite (qb _ tx)(hb _ tx) echelon_can_extensionE
               erecdef_powerset// - Hr //.
- move => x x' tx tx' Hx Hx'.
  move:(tree_to_echelon_ok tx) => [sa sb sc].
  move:(tree_to_echelon_ok tx') => [sa' sb' sc'].
  rewrite (qc _ _ tx tx')  (hc _ _ tx tx').
  by rewrite echelon_can_extensionE erecdef_product // -Hx// - Hx' //.
Qed.

Lemma cpred_pr0 a b: \0c <c a -> a <=c b -> natp b -> cpred a <c b.
Proof.
move => ra rb nN.
move:(cpred_pr  (NS_le_nat rb nN) (nesym (proj2 ra))) => [sa sb].
apply /(cleSlt0P (CS_nat sa) nN); ue.
Qed.

Lemma Eextension_prop_fct c E E' f
   (A :=  echelon_value c E)
   (A' :=  echelon_value c E')
   (g :=  echelon_extension c f):
   echelon c ->
   (forall i, i <c (esize c) -> inc (Vg f i) (functions (Vg E i) (Vg E' i))) ->
   forall i,  i <c (slength c) ->
   inc (Vg g i) (functions (Vg A i) (Vg A' i)).
Proof.
move => ha hb i im.
move: (slength_nat (proj1 (proj1 ha))) => mN.
have iN:= (NS_lt_nat im mN); move: i iN im.
apply: Nat_induction1.
move => i iN Hr lim.
move: (Eextension_prop f ha lim) (echelon_value_prop E ha lim) (echelon_value_prop E' ha lim).
simpl;set a := P _; set b := Q _; rewrite -/A -/A' -/g.
move => [pa pb pc][pa' pb' pc'][pa'' pb'' pc''].
case (p_or_not_p (a = \0c)) => az.
  move: (pa az) (pa' az) (pa'' az) => [/cge1P ra rb ->][_ _ ->] [_ _ ->].
  apply: (hb _(cpred_pr0 ra rb (NS_esize ha))).
case (p_or_not_p (b = \0c)) => bz.
  move: (pb bz) (pb' bz) (pb'' bz) => [ra rb ->][_ _ ->] [_ _ ->].
  move: (cpred_pr6' iN ra rb) =>[qa qb qc].
  apply: etp_fun; apply:Hr => //; exact: (clt_ltT qc lim).
move:(pc az bz) (pc' az bz)(pc'' az bz) =>
  [ra rb rc rd ->][_ _ _ _ ->] [_ _ _ _ ->].
move: (cpred_pr6' iN ra rb)  (cpred_pr6' iN rc rd) =>[qa qb qc][qa' qb' qc'].
apply: ext_to_prod_fun; apply: Hr => //.
 apply: (clt_ltT qc lim).
 apply: (clt_ltT qc' lim).
Qed.

Lemma Eextension_prop_inj c f (g := echelon_extension c f):
   echelon c ->
   (forall i, i <c (esize c) -> injection (Vg f i)) ->
   (forall i, i <c  (slength c) -> injection (Vg g i)).
Proof.
move => ha hc i im.
move: (slength_nat (proj1 (proj1 ha))) => mN.
have iN:= (NS_lt_nat im mN); move: i iN im.
apply: Nat_induction1 => k kN Hr lkn.
move: (Eextension_prop f ha lkn); simpl;set a := P _; set b := Q _.
move => [pa pb pc].
case (p_or_not_p (a = \0c)) => az.
  move: (pa az) => [/cge1P ra rb ->].
  apply: (hc _(cpred_pr0 ra rb (NS_esize ha))).
case (p_or_not_p (b = \0c)) => bz.
  move: (pb bz) => [ra rb ->].
  move:(cpred_pr6' kN ra rb) =>[qa qb qc].
  apply: etp_fi; apply:Hr => //; apply: (clt_ltT qc lkn).
move:(pc az bz) => [ra rb rc rd ->].
move:(cpred_pr6' kN ra rb) (cpred_pr6' kN rc rd)=>[qa qb qc][qa' qb' qc'].
apply: ext_to_prod_fi; apply: Hr => //.
 apply: (clt_ltT qc lkn).
 apply: (clt_ltT qc' lkn).
Qed.


Lemma Eextension_prop_surj  c f (g := echelon_extension c f):
   echelon c ->
   (forall i, i <c (esize c) -> surjection (Vg f i)) ->
   (forall i, i <c  (slength c) -> surjection (Vg g i)).
Proof.
move => ha hc i im.
move: (slength_nat (proj1 (proj1 ha))) => mN.
have iN:= (NS_lt_nat im mN); move: i iN im.
apply: Nat_induction1 => k kN Hr lkn.
move: (Eextension_prop f ha lkn); simpl;set a := P _; set b := Q _.
move => [pa pb pc].
case (p_or_not_p (a = \0c)) => az.
  move: (pa az) => [/cge1P ra rb ->].
  apply: (hc _(cpred_pr0 ra rb (NS_esize ha))).
case (p_or_not_p (b = \0c)) => bz.
  move: (pb bz) => [ra rb ->].
  move:(cpred_pr6' kN ra rb) =>[qa qb qc].
  apply: etp_fs; apply:Hr => //; apply: (clt_ltT qc lkn).
move:(pc az bz) => [ra rb rc rd ->].
move:(cpred_pr6' kN ra rb) (cpred_pr6' kN rc rd)=>[qa qb qc][qa' qb' qc'].
apply: ext_to_prod_fs; apply: Hr => //.
 apply: (clt_ltT qc lkn).
 apply: (clt_ltT qc' lkn).
Qed.

Lemma Eextension_prop_bij_inv c f (g := echelon_extension c f)
   (lif := Lg (esize c) (fun z => inverse_fun (Vg f z)))
   (lig := echelon_extension c lif):
   echelon c ->
   (forall i, i <c (esize c) -> bijection (Vg f i)) ->
   forall i, i <c  (slength c) ->
        bijection (Vg g i) /\ inverse_fun (Vg g i) = Vg lig  i.
Proof.
move => ha hc i im.
move: (slength_nat (proj1 (proj1 ha))) => mN.
have iN:= (NS_lt_nat im mN); move: i iN im.
have nN:=(NS_esize ha).
apply: Nat_induction1 => k kN Hr lkn.
move: (Eextension_prop f ha lkn)  (Eextension_prop lif ha lkn).
simpl;set a := P _; set b := Q _.
move => [pa pb pc] [pa' pb' pc']. 
case (p_or_not_p (a = \0c)) => az.
  move: (pa az) (pa' az)=> [/cge1P ra rb ->] [_ _ ->].
  have aux:= (cpred_pr0 ra rb (NS_esize ha)).
  by split; [ apply: (hc _ aux) | rewrite /Vl /lif LgV//;  apply /(NltP nN)].
case (p_or_not_p (b = \0c)) => bz.
  move: (pb bz)(pb' bz) => [ra rb ->][_ _ ->]. 
  move:(cpred_pr6' kN ra rb) =>[qa qb qc].
  move: (Hr _ qc (clt_ltT qc lkn)) => [sa sb].
  by move:(etp_inv sa) => [sc sd]; split => //; rewrite /Vl sd sb.
move:(pc az bz) (pc' az bz) => [ra rb rc rd ->] [_ _ _ _ ->].
move:(cpred_pr6' kN ra rb) (cpred_pr6' kN rc rd)=>[qa qb qc][qa' qb' qc'].
move:(Hr _ qc (clt_ltT qc lkn)) (Hr _ qc' (clt_ltT qc' lkn)).
move => [b1 i1][b2 i2];split; first by exact : (ext_to_prod_fb b1 b2).
by rewrite (ext_to_prod_inverse  b1 b2) // i1 i2.
Qed.



Lemma Eextension_prop_bijset c E E' f
   (A :=  echelon_value c E)
   (A' :=  echelon_value c E')
   (g :=  echelon_extension c f):
   echelon c ->
   (forall i, i <c (esize c) -> inc (Vg f i) (bijections (Vg E i) (Vg E' i))) ->
   forall i,  i <c (slength c) -> inc (Vg g i) (bijections (Vg A i) (Vg A' i)).
Proof.
move => ha hb i hc.
apply: Zo_i; first by apply: (Eextension_prop_fct ha) hc; move => j /hb /Zo_P[].
have ra:(forall i, i <c esize c -> bijection (Vg f i)).
  by  move => j /hb /Zo_P[].
by case:(Eextension_prop_bij_inv ha ra hc). 
Qed.

Lemma Eextension_prop_bijsetL c E E' f:
   echelon c ->
   \0c <c slength c ->
   (forall i, i <c esize c -> inc (Vg f i) (bijections (Vg E i) (Vg E' i))) ->
   inc (echelon_can_extension c f)
       (bijections (echelon_of_base c E) (echelon_of_base c E')).
Proof.
move => sa sb sc.
rewrite /echelon_can_extension/echelon_of_base.
have mN:= (slength_nat (proj1 (proj1 sa))).
have hd:= (cpred_lt mN (nesym (proj2 sb))).
exact: (Eextension_prop_bijset sa sc hd).
Qed.
  

Lemma Eextension_prop_id c f (g :=  echelon_extension c f)
   (is_identity := fun z => z = identity (source z)):
   echelon c ->
   (forall i, i <c esize c -> is_identity (Vg f i)) ->
   forall i, i <c slength c -> is_identity (Vg g i).
Proof.
move => ha hc i im.
move: (slength_nat (proj1 (proj1 ha))) => mN.
have iN:= (NS_lt_nat im mN); move: i iN im.
have Hb x: is_identity (identity x) by rewrite /is_identity; aw.
apply: Nat_induction1 => k kN Hr lkn.
move: (Eextension_prop f ha lkn); simpl;set a := P _; set b := Q _.
move => [pa pb pc].
case (p_or_not_p (a = \0c)) => az.
  move: (pa az) => [/cge1P ra rb ->].
  apply: (hc _(cpred_pr0 ra rb (NS_esize ha))).
case (p_or_not_p (b = \0c)) => bz.
  move: (pb bz) => [ra rb ->].
  move:(cpred_pr6' kN ra rb) =>[qa qb qc].
  move: (Hr _ qc (clt_ltT qc lkn)); rewrite /Vl -/g => ->.
  by rewrite etp_identity; apply: Hb.
move:(pc az bz) => [ra rb rc rd ->].
move:(cpred_pr6' kN ra rb) (cpred_pr6' kN rc rd)=>[qa qb qc][qa' qb' qc'].
move:(Hr _ qc (clt_ltT qc lkn)) (Hr _ qc' (clt_ltT qc' lkn)) => i1 i2.
rewrite -/g /Vl i1 i2  ext_to_prod_identity; apply: Hb.
Qed.


Lemma Eextension_prop_idL c f E:
   echelon c ->
   (forall i, i <c esize c -> (Vg f i) = identity (Vg E i)) ->
   \0c <c slength c ->
   (echelon_can_extension c f) = identity (echelon_of_base c E).
Proof.
set n := esize c; move => ha hb hc.
have hd:(forall i, i <c n-> Vg f i = identity (source (Vg f i))).
  by move => i lin; rewrite (hb _ lin); aw.
have hd': (forall i, i <c n -> inc (Vg f i) (functions (Vg E i) (Vg E i))).
  by move => i lin; rewrite(hb _ lin);apply/functionsP; apply: identity_prop.
have mN:= (slength_nat (proj1 (proj1 ha))).
have he:= (cpred_lt mN (nesym (proj2 hc))).
move: (Eextension_prop_id ha hd he). 
by move /functionsP: (Eextension_prop_fct ha hd' he)=> [_ -> _].
Qed.
  
Lemma Eextension_prop_comp c f f' E E' E'' (m := slength c)
   (n:=  esize c)
   (f'' := Lg n (fun z =>  (Vg f' z) \co (Vg f z)))
   (g := echelon_extension c f)
   (g' := echelon_extension c f')
   (g'':= echelon_extension c f''):
   echelon c ->
   (forall i, i <c n -> inc (Vg f i) (functions (Vg E i) (Vg E' i))) ->
   (forall i, i <c n -> inc (Vg f' i) (functions (Vg E' i) (Vg E'' i))) ->
   forall i, i <c m -> Vg g'' i = (Vg g' i) \co (Vg g i).
Proof.
move => ha hb hc.
set (A :=  echelon_value c E).
set (A' :=  echelon_value c E').
set (A'':=  echelon_value c E'').
have hb': forall i, i <c m -> inc (Vg g i) (functions (Vg A i) (Vg A' i)).
  by move => i lim;  apply:  Eextension_prop_fct.
have hc': forall i, i <c m -> inc (Vg g' i) (functions (Vg A' i) (Vg A'' i)).
  by move => i lim; by apply:  Eextension_prop_fct.

move: (slength_nat (proj1 (proj1 ha))) => mN i lim.
have iN:= (NS_lt_nat lim mN); move: i iN lim.
have nN:=(NS_esize ha).
apply: Nat_induction1.

move => k kN Hr lt.
move: (Eextension_prop f ha lt) (Eextension_prop f' ha lt)
                                (Eextension_prop f'' ha lt).
simpl;set a := P _; set b := Q _.
move => [pa pb pc] [pa' pb' pc'] [pa'' pb'' pc''].
case (p_or_not_p (a = \0c)) => az.
  move: (pa az) (pa' az) (pa'' az) => [/cge1P ra rb ->]  [_ _ ->] [_ _ ->].
  move: (cpred_pr0 ra rb nN) => w.
  by rewrite /Vl /f'' LgV//;  apply /(NltP nN).
case (p_or_not_p (b = \0c)) => bz.
  move: (pb bz)(pb' bz)(pb'' bz) => [ra rb ->] [ _ _ ->][_ _ ->].
  move:(cpred_pr6' kN ra rb) =>[qa qb qc]; have W:= (clt_ltT qc lt).
  move: (hb' _ W) (hc' _ W) => i1 i2.
  by rewrite /Vl -/g -/g' - (etp_comp i1 i2) - (Hr _ qc W).
move:(pc az bz)(pc' az bz) (pc'' az bz)
  => [ra rb rc rd ->] [_ _ _ _ ->] [ _ _ _ _ ->].
move:(cpred_pr6' kN ra rb) (cpred_pr6' kN rc rd)=>[qa qb qc][qa' qb' qc'].
have W := (clt_ltT qc lt); have W' := (clt_ltT qc' lt).
move:(Hr _ qc W) (Hr _ qc' W') => i1 i2.
move:(hc'  _ W)(hb'  _ W)(hc'  _ W') (hb'  _ W')=> ia ib ic id.
by rewrite /Vl (ext_to_prod_comp ib id ia ic) /f''  i1 i2.
Qed.

Lemma Eextension_prop_composable c f f'
   (g := echelon_extension c f)
   (g' := echelon_extension c f'):
   echelon c ->
   (forall i, i <c esize c ->  (Vg f' i) \coP (Vg f i)) ->
   forall i,i <c (slength c) -> (Vg g' i) \coP (Vg g i).
Proof.
move => h ha.
have nN:=(NS_esize h); set n := esize c.
pose E := Lg n (fun i => source (Vg f i)).
pose E' := Lg n (fun i => target (Vg f i)).
pose E'' := Lg n (fun i => target (Vg f' i)).
have hb:
  (forall i, i <c n -> inc (Vg f i) (functions (Vg E i) (Vg E' i))).
  move => i lin; move:(ha _ lin) => [_ fa _];apply/functionsP; split => //.
    by rewrite /E  LgV//; apply /(NltP nN).
    by rewrite /E' LgV//; apply /(NltP nN).
have hc:
  (forall i, i <c n -> inc (Vg f' i) (functions (Vg E' i) (Vg E'' i))).
  move => i lin; move:(ha _ lin) => [fa _ fb];apply/functionsP; split => //.
    by rewrite /E' LgV//; apply /(NltP nN).
    by rewrite /E'' LgV//; apply /(NltP nN).
move => i lim.
move: (Eextension_prop_fct h hc lim) => /functionsP [ra rb rc].
move: (Eextension_prop_fct h hb lim) => /functionsP [ra' rb' rc'].
by split => //;rewrite rb rc'. 
Qed.



(** Transportability *)

Definition slist_append x y :=
  let n := slength x in let m := slength y in 
  Lg (n +c m) (fun z => Yo (z <c n) (Vg x z) (Vg y (z -c n))).

Definition Typ_with_id f A :=
  slist_append f (Lg (domain A) (fun z => identity (Vg A z))). 


Lemma slist_append_list x y: slistp x -> slistp y -> 
  slistp (slist_append x y) /\
  slength (slist_append x y) = slength x +c slength y.
Proof.
move=> ha hb.
move:(slength_nat ha)(slength_nat hb) => nN mN.
have nmM:=(NS_sum nN mN).
have d: (domain (slist_append x y)) = (slength x +c slength y). 
  by  rewrite /slist_append; aw.
by rewrite /slistp /slength d; split => //; split => //; apply:Lg_fgraph. 
Qed.

Lemma slist_append_val1 x y i: slistp x -> slistp y -> 
  i<c slength x -> Vg (slist_append x y) i = Vg  x i.
Proof.
move => ha hb hc.
move:(slength_nat ha)(slength_nat hb) => nN mN.
have hi: inc i (slength x +c slength y).
  by apply /(NltP (NS_sum nN mN)); apply: (clt_leT hc); apply:Nsum_M0le.
by rewrite /slist_append LgV //; Ytac0.
Qed.
 

Lemma slist_append_val2 x y i: slistp x -> slistp y -> 
  i<c slength y -> Vg (slist_append x y) ((slength x) +c i) = Vg y i.
Proof.
move => ha hb hc.
move:(slength_nat ha)(slength_nat hb) => nN mN.
have hi: inc (slength x +c i) (slength x +c slength y).
  by apply  /(NltP (NS_sum nN mN)); apply:csum_Meqlt.
have iN:=(NS_lt_nat hc mN).
move:(Nsum_M0le i nN); rewrite {1} csumC => /cleNgt bad.
by rewrite /slist_append (LgV hi) (csumC _ i) (cdiff_pr1 iN nN); Ytac0.
Qed.

Lemma slist_emptyp l: slistp l -> slength l = \0c -> l = emptyset. 
Proof.
move => sa sb.
move: (slist_domain sa); rewrite sb Nint_co00 => dle.
by apply/set0_P => x /domain_i1; rewrite dle => /in_set0.
Qed.




Lemma Typ_with_id_prop n S f x y A :
  slistpl x n -> slistpl y n -> slistpl f n ->
  slistp A -> echelon S -> slength S <> \0c -> esize S <=c n +c slength A ->
  (forall i, i <c n -> inc (Vg f i) (bijections (Vg x i) (Vg y i))) ->
   inc (echelon_can_extension S (Typ_with_id f A)) 
    (bijections (echelon_of_base S (slist_append x A))
                        (echelon_of_base S (slist_append y A)) ).
Proof.
move => [lx sx][ly sy] [lf sf] lA eS snt sS hd.
rewrite /echelon_can_extension /echelon_of_base.
have he:=(cpred_lt (proj2 (proj1 (proj1 eS))) snt).
apply:(Eextension_prop_bijset eS _ he) => j jle.
rewrite /Typ_with_id; set ff := Lg _ _. 
have nN: natp n by rewrite - sf; exact (proj2 lf).
have lAN: natp (domain A) by exact: (proj2 lA).
have lff: slistp ff by rewrite /ff; split; aw; fprops.
move:(clt_leT jle sS); rewrite csumC => jsa.
have jN: natp j by exact: (NS_lt_nat jsa (NS_sum lAN nN)).
case:(NleT_el nN jN) => js.
  move: (cdiff_pr js) => js1; rewrite - js1.
  have js3:=(cdiff_Mlt lAN jN js jsa).
  have js2:  j -c n <c slength ff by  rewrite /ff; aw.
  have js4: inc (j -c n) (domain A) by apply/(NltP lAN).
  rewrite -{1} sf (slist_append_val2 lf lff js2).
  rewrite -{2} sx (slist_append_val2 lx lA js3).
  rewrite -{3} sy (slist_append_val2 ly lA js3).
  rewrite /ff LgV//; apply/bijectionsP; rewrite/bijection_prop; aw; split => //.
  exact: identity_fb. 
have sl': j <c slength f by rewrite sf.
have sx': j <c slength x by rewrite sx.
have sy': j <c slength y by rewrite sy.
rewrite (slist_append_val1 lf lff sl').
rewrite (slist_append_val1 lx lA sx').
by rewrite (slist_append_val1 ly lA sy'); apply: hd.
Qed.

Lemma Typ_with_id_prop2 n S f x A:
  slistpl x n -> slistpl f n ->
  slistp A -> echelon S -> slength S <> \0c -> esize S <=c n +c slength A ->
  n = \0c -> 
    echelon_can_extension S (Typ_with_id f A) =
   identity (echelon_of_base S (slist_append x A)).
Proof.
move => [xl sx] [lf sf] lA eS snt sS nz.
have slAc:= (CS_nat (proj2 lA)).
move: sS; rewrite nz (csum0l slAc) => eq1.
move: (CS_nat (proj2 (proj1 (proj1 eS)))) => cb.
have sp:=(card_ne0_pos cb snt).
apply: (Eextension_prop_idL eS _ sp) => k kl.
have kp:k <c domain A by apply: (clt_leT kl eq1).
have hw:= (csum0l (proj31_1 kl)).
have kda: inc k (domain A) by apply/(NltP (proj2 lA)).
move: (slist_append_val2 xl lA kp); rewrite sx nz hw => ->.
rewrite /Typ_with_id; set ff := Lg _ _.
have lff: slistp ff by rewrite /ff;split; fprops; aw; exact (proj2 lA).
have sff: slength ff = domain A by rewrite /ff/slength; aw.
rewrite - sff in kp.
by move: (slist_append_val2 lf lff kp); rewrite sf nz hw /ff LgV.
Qed.

  
Definition Typ_auxg n A S :=
  [/\ natp n, slistp A, slistp S &
     forall i, inc i (domain S) -> 
       echelon (Vg S i) /\ esize (Vg S i) <=c n +c slength A].

Definition Typ_schemeg x A S i:=
  Yo (slength (Vg S i) = \0c) emptyset (echelon_of_base (Vg S i) (slist_append x A)).
  
Definition Typificationg n A S x s :=
  [/\ Typ_auxg n A S, slistpl x n, slistpl s (slength S) &
   forall i, i <c  slength s -> inc (Vg s i) (Typ_schemeg x A S i)].


Definition Typ_aux n A S :=
  [/\ natp n, slistp A,  echelon S & esize S <=c n +c slength A].

Definition Typ_scheme x A S:=
  Yo (slength S = \0c) emptyset (echelon_of_base S (slist_append x A)).
  
Definition Typification n A S x s :=
  [/\ Typ_aux n A S, slistpl x n & inc s (Typ_scheme x A S)].


Definition Typ_hypg n x A S s y f :=
  [/\ Typificationg n A S x s, slistpl y n, slistpl f n & 
   forall i, i <c n -> inc (Vg f i) (bijections (Vg x i) (Vg y i))].


Definition Typ_concg (x:Set) A S s y f R :=
  let s' := Lg (domain S)
   (fun i => Vf (echelon_can_extension (Vg S i) (Typ_with_id f A)) (Vg s i))
  in R x s <-> R y s'.

Definition Transportableg n A S R:= 
  forall x s y f, Typ_hypg n x A S s y f ->  Typ_concg x A S s y f R.


Definition Typ_hyp n x A S s y f :=
  [/\ Typification n A S x s, slistpl y n, slistpl f n & 
   forall i, i <c n -> inc (Vg f i) (bijections (Vg x i) (Vg y i))].


Definition Typ_conc (x:Set) A S s y f R :=
  let s' :=  Vf (echelon_can_extension S (Typ_with_id f A)) s
  in R x s <-> R y s'.

Definition Transportable n A S R:= 
  forall x s y f, Typ_hyp n x A S s y f ->  Typ_conc x A S s y f R.

Lemma transportable_casep1 n A S R (R' := fun x s => R x (Vg s \0c)):
 Transportable n A S R <->
 Transportableg n A (Lg \1c (fun z => S)) R'.
Proof.
have i01: inc \0c \1c by apply: set1_1.
have ww: inc \0c (domain (Lg \1c (fun _ : Set => S))) by aw.
rewrite /Transportable /Transportableg; split.
  move => ha x s' y f [ [q1 q2 q3 q4] qb qc qd].
  case: q1; case: q3; rewrite /slength Lgd => ua ub nN lA lsp lv.
  move:(lv _ i01); rewrite LgV// => - [es1 es2].
  have: \0c <c slength s' by rewrite /slength ub; apply:clt_01.
  move/q4; rewrite /Typ_schemeg. rewrite LgV // => xx.
  by rewrite /Typ_concg /R' LgV // LgV //; apply: ha.
move => ha x s y f [ [[q1a q1b q1c q1d] q2 q3] qb qc qd]. 
move:(ha x (Lg \1c (fun z => s)) y f). rewrite  /Typ_concg /R'.
rewrite (LgV i01) (LgV ww) (LgV i01) (LgV i01); apply.
split => //; split.
- split => //; rewrite /slistp; aw; fprops => i i1; rewrite LgV//.
- done.
- rewrite/slistpl /slistp; aw; split; fprops.  
- rewrite /Typ_schemeg /slength; aw; move => i /(NltP NS1) => i1.
  rewrite  ! LgV//.
Qed.
  

Lemma transportable_aux1 n x A S s y f
  ( s' := Lg (domain S)
   (fun i => Vf (echelon_can_extension (Vg S i) (Typ_with_id f A)) (Vg s i))):
  Typ_hypg n x A S s y f ->
  Typificationg n A S y s'.
Proof.
move =>[[qa qb qc qd] hb hc hd].
set p := slength S; have qv := proj2 qc; rewrite qv in qd.
have pN: natp p by rewrite /p;move : qc => [[ _ h] <-].
have ls': slistpl s' (slength S) by rewrite /s'; split; aw; split;aw; fprops.
have eq2:= (proj2 qc).
split => //; rewrite /s'; aw => i ils.
have ids: inc i (domain S)  by apply/(NltP pN).
rewrite LgV//.
move:(qd _ ils); rewrite /Typ_schemeg; Ytac w; first by move/in_set0.
Ytac0.
set G := (echelon_can_extension (Vg S i) (Typ_with_id f A)).
suff: inc G (bijections (echelon_of_base (Vg S i) (slist_append x A))
                        (echelon_of_base (Vg S i) (slist_append y A)) ).
  by move /bijectionsP => [[[fg _] _] <- <-]; fprops.
move:(qa) => [_ slA _ h]; move: (h _ ids) => [ec ecx].
by apply: (Typ_with_id_prop qb hb hc slA ec w ecx hd).
Qed.

Lemma transportable_typificationg n A S:
  Typ_auxg n A S -> Transportableg n A S (Typificationg n A S).
Proof.
move => h x s y f H; move:(transportable_aux1 H) => h1.
by split => //; case:H.
Qed.


Lemma transportable_typification n A S:
  Typ_aux n A S -> Transportable n A S (Typification n A S).
Proof.
move => h; apply/transportable_casep1 => x s y f aux1. 
move: (aux1) (set1_1 \0c)=> [h2a h2b h2c h2d] i01.
set S' :=  (Lg \1c (fun _ : Set => S)).
have ls: slistp S' by rewrite /S';split; aw; fprops.
have zds: inc \0c (domain S') by rewrite /S';aw. 
have ha: Typ_auxg n A S'.
  by move: h => [h1 h2 h3 h4];split => //; rewrite /S';aw => i li1; rewrite LgV.
have hv: inc (Vg s \0c) (Typ_scheme x A S).
   move: h2a => [_ _ hu hv]; move: (proj2 hu); aw => sll; rewrite sll in hv.
   by move:(hv _ clt_01); rewrite /Typ_schemeg/S'; rewrite LgV.
have slxn: slistpl x n by case: h2a.
split => _ ; last by split.
have zds': \0c <c  domain S' by rewrite /S'; aw; apply:clt_01.
have ww: (Typ_schemeg y A S' \0c)  = (Typ_scheme y A S). 
rewrite /Typ_schemeg /Typ_scheme /S' LgV //.
move:(@transportable_aux1 n x A S' s y f aux1) => [qa qb qc]; aw => qd. 
by move: (qd _ zds'); rewrite LgV//; rewrite ww; split.
Qed.

Lemma transportable_spec1 n A S R: 
   n = \0c -> Typ_auxg n A S -> Transportableg n A S R.
Proof.
move => nz  [ha hb hc hd] x s y f [[pa pb pc pd] hf hg _].
rewrite nz in hf pb.
rewrite (slist_emptyp (proj1 pb) (proj2 pb)).
rewrite (slist_emptyp (proj1 hf) (proj2 hf)).
rewrite /Typ_concg; set s' := Lg _ _.
move: pc => [pc1 pc2].
have dd1: domain s = domain S.
  by rewrite   (slist_domain pc1) pc2 (slist_domain hc).
have dd: domain s = domain s' by rewrite /s' Lgd.  
suff: s = s' by move => ->; split.
apply: fgraph_exten; [ exact  (proj1 pc1) | rewrite /s'; fprops | done | ].
rewrite dd1; move => i ids /=; rewrite /s' LgV//.
have lis: i <c slength s.
  apply /(NintP (slength_nat pc1)).
  by rewrite - (slist_domain pc1) dd1.
move: (pd _ lis); rewrite /Typ_schemeg; Ytac sz; first by  move/in_set0.
rewrite nz in hg.
move: (hd _ ids) => [ua]; rewrite nz  => eq1 ww.
by rewrite(Typ_with_id_prop2 pb hg hb ua sz eq1 (erefl \0c)) idV.
Qed.

Definition equipotent_fam n x y :=
  forall i, i<c n -> cardinal (Vg x i) = cardinal (Vg y i).

Lemma transportable_spec_p0 n A S R: 
  slength S = \0c ->  Typ_auxg n A S ->
  (Transportableg n A S R <->
    (forall x y, slistpl x n -> slistpl y n -> equipotent_fam n x y ->
      (R x emptyset <-> R y emptyset))).
Proof.
move => h1 ts; move: (ts)=> [nN _ lS _].
split.
   move => TT x y [xl xs] [yl ys] eq.
   set f := Lg n (fun z => (equipotent_ex (Vg x z) (Vg y z))).
   have lf: slistpl f n. 
     split; last by rewrite /slength /f;aw.
     split; rewrite/f; aww; by exists n.
   have s0:domain emptyset = \0c by rewrite domain_set0. 
   have le: slistpl emptyset (slength S).
     rewrite h1; split =>//;split;try apply:fgraph_set0.
       by rewrite s0;apply:NS0.
   have ha: Typificationg n A S x emptyset.
     by split => // i; rewrite /slength s0 => /clt0.  
   have hb: Typ_hypg n x A S emptyset y f.  
     split => // i lin; move/ (NltP nN): (lin) => lin1.
     apply/bijectionsP; rewrite /f LgV//; apply: equipotent_ex_pr.
     by apply/card_eqP; apply: eq.
   move:(TT x emptyset y f hb); rewrite /Typ_concg (slist_emptyp lS h1).
   by rewrite domain_set0 /Lg funI_set0.
move => Hxy x s y f [ha hb hc hd].
rewrite /Typ_concg (slist_emptyp lS h1)  domain_set0 /Lg funI_set0.
move:ha => [_ he ls _]; rewrite h1 in ls.
rewrite (slist_emptyp (proj1 ls) (proj2 ls)); apply: Hxy => //.
by move => i /hd /bijectionsP bp; apply /card_eqP;  exists (Vg f i).
Qed.


Lemma transportable_spec3 n A S R: 
  (forall x s s', Typificationg n A S x s -> Typificationg n A S x s' ->
                  (R x s <-> R x s')) ->
  Typ_auxg n A S ->
  (Transportableg n A S R <->
    (forall x y, slistpl x n -> slistpl y n -> equipotent_fam n x y ->
       (forall u v, Typificationg n A S x u -> Typificationg n A S y v ->
            (R x u <-> R y v)))).
Proof.
move =>  h0 ts; move: (ts)=> [nN _ lS _].
split.
  move => TT x y [xl xs] [yl ys] eq1 s v hu hv.
  set f := Lg n (fun z => (equipotent_ex (Vg x z) (Vg y z))).
  have lf: slistpl f n. 
    split; last by rewrite /slength /f;aw.
    by split; rewrite/f; fprops; aw.
  have fp: forall i, i <c n -> inc (Vg f i) (bijections (Vg x i) (Vg y i)).
    move => i lin; rewrite/f LgV//; last by apply/(NltP nN).
    by apply/bijectionsP/equipotent_ex_pr /card_eqP /eq1.
  have HA:(Typ_hypg n x A S s y f) by [].
  move: (transportable_aux1 HA) (TT _ _ _  _ HA) => sa sb.
  apply:(iff_trans sb); apply:(h0 _ _ _ sa hv).
move => H x s y f [Ti ly lf hd]. 
have ra: slistpl x n by case: Ti.
have rb: equipotent_fam n x y.
  by move => i /hd /bijectionsP bp; apply/card_eqP;exists (Vg f i).
have rc: forall i, i <c slength S -> nonempty (Typ_schemeg x A S i).
  by move: Ti => [_ _ [_ ->]] h i /h hi; exists (Vg s i).
apply: H => //.
have /transportable_aux1 //: Typ_hypg n x A S s y f by [].
Qed.

Lemma slistp_0: slistpl emptyset \0c.
Proof.
move: (fgraph_set0) NS0 => ha hb.
by rewrite /slistpl /slistp /slength domain_set0.
Qed.

Lemma slist_append_empty x: slistp  x -> slist_append x emptyset = x.
Proof.
move => [fgx lx].
rewrite /slist_append /slength; aw; rewrite (csum0r (CS_nat lx)).
apply: fgraph_exten; [ fprops | done | by aw | aw] => i idg.
by rewrite (LgV idg) Y_true //; apply/(NltP lx).
Qed.


Lemma Typ_with_id_empty x: slistp  x -> Typ_with_id x emptyset = x.
Proof.
rewrite /Typ_with_id domain_set0 /Lg funI_set0;apply:slist_append_empty. 
Qed.




Section Example1.


Lemma echelon_trivial n (S:= slist1 (J \0c n)): natp n -> n <> \0c ->
   echelon S /\ esize S = n.
Proof.
move: NS0 clt_01=> ns0 lt01 nN np.
move: (slist1_prop (J \0c n)) => [[ha hb] hc].
have es: echelon S.
  split; first by split => // t /Lg_range_P [_ _ ->]; apply:setXp_i.
  by rewrite hb => i /clt1 ->; rewrite hc /=; aw; split.
split => //; apply: (esize_prop2 es); rewrite hb; first by  exists \0c.
move => j /clt1->; rewrite hc pr2_pair => _; exact: (cleR (CS_nat nN)).
Qed.

Lemma echelon_trivial_value n (S:= slist1 (J \0c n)) E: 
  natp n -> n <> \0c ->
  echelon_of_base S E = (Vl E n).
Proof.
move => nN np.
move: (slist1_prop (J \0c n)) => [[ha hb] hc].
move:(echelon_trivial nN np) => [pa pb].
rewrite /echelon_of_base hb /Vl cpred1.
have w1: \0c <c slength S by rewrite hb; exact: clt_01.
move: (proj31 (echelon_value_prop E pa w1)); rewrite hc; aw => h1.
by case: (h1 (erefl \0c)).
Qed.


Lemma echelon_trivial_extension n (S:= slist1 (J \0c n)) E: 
  natp n -> n <> \0c ->
  echelon_can_extension S E = (Vl E n).
Proof.
move => nN np.
move: (slist1_prop (J \0c n)) => [[ha hb] hc].
move:(echelon_trivial nN np) => [pa pb].
rewrite /echelon_can_extension hb /Vl cpred1.
have w1: \0c <c slength S by rewrite hb; exact: clt_01.
move: (proj31 (Eextension_prop E pa w1)); rewrite hc; aw => h1.
by case: (h1 (erefl \0c)).
Qed.



  
Definition Ex_scheme1 := slist2 (slist1 (J \0c \1c))  (slist1 (J \0c \1c)).
Definition Ex_scheme2 := slist2 (slist1 (J \0c \1c))  (slist1 (J \0c \2c)).

Lemma Ex_typ_aux1: Typ_auxg  \2c emptyset  Ex_scheme1.
Proof. 
move:cle_12 slistp_0 NS2 => cle12 [ha hb] ns2; rewrite /Ex_scheme1.
set S1 := (slist1 (J \0c \1c)).
move: (slist2_prop  S1 S1) => [[hc hd]  he hf].
move: (echelon_trivial NS1 card1_nz) => [p1 p2].
split => //; rewrite [domain _]hd hb (csum0r CS2) => i /set2_P [] ->.
by rewrite he p2.
by rewrite hf p2.
Qed.
  

Lemma Ex_typ_aux2: Typ_auxg  \2c emptyset  Ex_scheme2.
Proof. 
move:(cleR CS2) cle_12 slistp_0 NS2 => c2 l2 [ha hb] ns2; rewrite /Ex_scheme1.
set S1 := (slist1 (J \0c \1c)).
set S2 := (slist1 (J \0c \2c)).
move: (slist2_prop  S1 S2) => [[hc hd]  he hf].
move: (echelon_trivial NS1 card1_nz) => [p1 p2].
move: (echelon_trivial NS2 card2_nz) => [p1' p2'].
split => //; rewrite [domain _]hd hb (csum0r CS2) => i /set2_P [] ->.
by rewrite he p2.
by rewrite hf p2'.
Qed.


Lemma Ex_transportable1:
  Transportableg \2c emptyset  Ex_scheme1 (fun _ s => Vg s \0c = Vg s \1c). 
Proof.
move => x s y f [ha hb hc hd].
move: NS1  card1_nz => ns1 c1nz.
move: (slist2_prop (slist1 (J \0c \1c))  (slist1 (J \0c \1c))).
  move => [qa qb qc].
have hw: natp (slength Ex_scheme1) by rewrite/Ex_scheme1; aw; apply: NS2.
have hu: inc \1c (domain Ex_scheme1) by rewrite /Ex_scheme1; aww.
have hv: inc \0c (domain Ex_scheme1) by rewrite /Ex_scheme1; aww.
have hv': \0c <c slength Ex_scheme1 by  apply/(NltP).
have hu': \1c <c slength Ex_scheme1 by  apply/(NltP).
rewrite /Typ_concg LgV// LgV//.
rewrite (Typ_with_id_empty  (proj1 hc)) qb qc echelon_trivial_extension //.
rewrite /Vl cpred1; split => h; first by rewrite h.
move: ha => [k1 k2 k3 k4].
rewrite (proj2 k3) in k4. move:(k4 _ hv') (k4 _ hu').
rewrite /Typ_schemeg qb qc echelon_trivial_value //.
rewrite  (slist_append_empty (proj1 k2)); Ytac w2; first by move/in_set0.
rewrite /Vl cpred1 => ua ub.
move: (hd _ (clt_02)) => /bijectionsP [[fa fb] fc fd]; apply:(proj2 fa).
  by rewrite fc.
  by rewrite fc.
done.
Qed.

  
Lemma Ex_transportable2:
  ~ Transportableg \2c emptyset  Ex_scheme1 (fun x _ => Vg x \0c = Vg x \1c). 
Proof.
move: NS1 card1_nz => qa qb.
set x := slist2 (singleton \0c)(singleton \1c).
set y := slist2 (singleton \0c)(singleton \0c).
set s := slist2 \0c \0c.
set f1 := identity (singleton \0c).
set f2 := Lf  (fun z => \0c) (singleton \1c)(singleton \0c).
set f := slist2 f1 f2.
move: (slist2_prop (singleton \0c)(singleton \1c)) => [xp1 xp2 xp3].
move: (slist2_prop (singleton \0c)(singleton \0c)) => [yp1 yp2 yp3].
move: (slist2_prop f1 f2) => [fp1 fp2 fp3].
move: (slist2_prop \0c \0c) => [sp1 sp2 sp3].
have hu: (slength Ex_scheme1) = \2c by rewrite /slength /Ex_scheme1; aw.
set S := (slist1 (J \0c \1c)).
move: (slist2_prop S S); rewrite /= -/Ex_scheme1 => -[Sp1 Sp2 Sp3].
have snz: (slength S <> \0c)by rewrite /S/slength/slist1; aw.
have ha: Typificationg \2c emptyset Ex_scheme1 x s.
  split; [ exact:Ex_typ_aux1 | done | by rewrite hu | ].
  rewrite /Typ_schemeg (slist_append_empty (proj1 xp1)) (proj2 sp1).
  move => i /clt2 [] ->; rewrite ?Sp2 ?Sp3 echelon_trivial_value//;Ytac0.
  - by rewrite /Vl cpred1 xp2 sp2; fprops.
  - by rewrite /Vl cpred1 xp2 sp3; fprops.
have hb: Typ_hypg \2c x emptyset Ex_scheme1 s y f.
   split => //i /clt2 [] ->.
   - rewrite xp2 yp2 fp2/f1; apply/bijectionsP; saw; apply: identity_fb.
   - rewrite xp3 yp3 fp3 /f2;apply/bijectionsP; saw.
     apply:lf_bijective.
     + by move => t _;fprops.
     + by move => u v /set1_P -> /set1_P ->.
     + by  move => u /set1_P ->; exists \1c; fprops.
move => h; move:(h x s y f hb).
rewrite /Typ_concg xp2 xp3 yp2 yp3 => bad.
move/bad: (erefl (singleton \0c)) => /(f_equal (inc \0c)) hh.
by move: (set1_1 \0c); rewrite hh => /set1_P e01; case:qb.
Qed.

Lemma Ex_transportable3:
  ~ Transportableg \2c emptyset  Ex_scheme2 (fun _ s => Vg s \0c = Vg s \1c). 
Proof.
move: NS1 card1_nz NS2 card2_nz => qa qb qc qd.
set x := slist2 (singleton \0c)(singleton \1c).
set y := slist2 (singleton \0c)(singleton \0c).
set s := slist2 \0c \1c.
set f1 := identity (singleton \0c).
set f2 := Lf  (fun z => \0c) (singleton \1c)(singleton \0c).
set f := slist2 f1 f2.
move: (slist2_prop (singleton \0c)(singleton \1c)) => [xp1 xp2 xp3].
move: (slist2_prop (singleton \0c)(singleton \0c)) => [yp1 yp2 yp3].
move: (slist2_prop f1 f2) => [fp1 fp2 fp3].
move: (slist2_prop \0c \1c) => [sp1 sp2 sp3].
have hu: (slength Ex_scheme2) = \2c by rewrite /slength /Ex_scheme2; aw.
set S1 := (slist1 (J \0c \1c)).
set S2 := (slist1 (J \0c \2c)).
move: (slist2_prop S1 S2); rewrite /= -/Ex_scheme2 => -[Sp1 Sp2 Sp3].
have snz: (slength S1 <> \0c)by rewrite /S1/slength/slist1; aw.
have snz': (slength S2 <> \0c)by rewrite /S2/slength/slist1; aw.
have cp2: (cpred \2c) = \1c by rewrite -(cpred_pr2 NS1) succ_one.
have ha: Typificationg \2c emptyset Ex_scheme2 x s.
  split; [ exact:Ex_typ_aux2 | done | by rewrite hu | ].
  rewrite /Typ_schemeg (slist_append_empty (proj1 xp1)) (proj2 sp1).
  move => i /clt2 [] ->; rewrite ?Sp2 ?Sp3 echelon_trivial_value//;Ytac0.
  - by rewrite /Vl cpred1 xp2 sp2; fprops.
  - by rewrite /Vl cp2 xp3 sp3; fprops.
have ax1: lf_axiom (fun z => \0c) (singleton \1c) (singleton \0c).
   by  move => t _;fprops.
have hb: Typ_hypg \2c x emptyset Ex_scheme2 s y f.
   split => //i /clt2 [] ->.
   - rewrite xp2 yp2 fp2/f1; apply/bijectionsP; saw; apply: identity_fb.
   - rewrite xp3 yp3 fp3 /f2;apply/bijectionsP; saw.
     apply:lf_bijective.
     + exact: ax1.
     + by move => u v /set1_P -> /set1_P ->.
     + by  move => u /set1_P ->; exists \1c; fprops.
move => h; move:(h x s y f hb).
have ra: inc \1c (domain Ex_scheme2) by rewrite /Ex_scheme2; aww.
have rb: inc \0c (domain Ex_scheme2) by rewrite /Ex_scheme2; aww.
rewrite /Typ_concg LgV// LgV//.
rewrite (Typ_with_id_empty (proj1 fp1)) Sp2 Sp3 !echelon_trivial_extension //.
rewrite /Vl cpred1 cp2 fp2 fp3 sp2 sp3 /f1 /f2 LfV // ? id_V //; fprops.
bw; fprops;move => k;move/k: (erefl \0c);fprops.
Qed.

End Example1.

Definition species_of_structure n A S R:=
  [/\ Typ_aux n A S, n <> \0c, slength S <> \0c & Transportable n A S R].

Lemma species_of_structure_typification n A S R x s :
   species_of_structure n A S R ->
   (Typification n A S x s  <-> 
      (slistpl x n /\ inc s  (echelon_of_base S (slist_append x A)))).
Proof.
move => [h1 h2 h3 h4]; split.
  by move => [u1 u2]; rewrite/Typ_scheme; Ytac0. 
by move => [qa qb]; rewrite/Typification /Typ_scheme; Ytac0.
Qed.


Definition structure_of_species n A S R E U:=
  species_of_structure n A S R /\ Typification n A S E U.

Definition set_of_structure_of_species  A S R E :=
  Zo (echelon_of_base S (slist_append E A)) (R E).

(* noter *)


Section Example2.
Definition Tree_ex1 := (Tp (Tx (Tb \0c)(Tb \0c))).
Definition Tree_ex2 := (Tp (Tx (Tx (Tb \0c)(Tb \0c)) (Tb \0c))).
Definition Tree_ex3 := (Tp (Tp (Tb \0c))).

Definition Echelon_ex1 := tree_to_echelon Tree_ex1.
Definition Echelon_ex2 := tree_to_echelon Tree_ex2.
Definition Echelon_ex3 := tree_to_echelon Tree_ex3.

Lemma cmax00: cmax \0c \0c = \0c.
Proof. by rewrite (cmax_xy (cleR CS0)). Qed.


Lemma Tree_ex1_prop : treep Tree_ex1 /\ tree_size Tree_ex1 = \0c.
Proof.
move:tdepth_prop_inv => [ha hb hc].
move:tree_size_p => [qa qb qc].
move:(proj1 (ha _ NS0)) (qa _ NS0) => r1 r2.
move:(proj1 (hc _ _ r1 r1)) (qc _ _ r1 r1); rewrite r2 cmax00 => r3 r4.
split; [exact:(proj1 (hb _ r3)) | by  move:(qb _ r3); rewrite r4 ].
Qed.

  
Lemma Tree_ex2_prop : treep Tree_ex2 /\ tree_size Tree_ex2 = \0c.
Proof.
move:tdepth_prop_inv => [ha hb hc].
move:tree_size_p => [qa qb qc].
move:(proj1 (ha _ NS0)) (qa _ NS0) => r1 r2.
move:(proj1 (hc _ _ r1 r1)) (qc _ _ r1 r1); rewrite r2 cmax00 => r3 r4.
move:(proj1 (hc _ _ r3 r1)) (qc _ _ r3 r1); rewrite r2 r4 cmax00 => r5 r6.
split; [exact:(proj1 (hb _ r5)) | by  move:(qb _ r5); rewrite r6 ].
Qed.

Lemma Tree_ex3_prop : treep Tree_ex3 /\ tree_size Tree_ex3 = \0c.
Proof.
move:tdepth_prop_inv => [ha hb hc].
move:tree_size_p => [qa qb qc].
move:(proj1 (ha _ NS0)) (qa _ NS0) => r1 r2.
move:(proj1 (hb _ r1)) (qb _ r1) => r3 r4.
split; [exact:(proj1 (hb _ r3)) | by move:(qb _ r3); rewrite r4 r2].
Qed.

Definition echelon_s1 c := [/\ echelon c, slength c <> \0c & esize c = \1c].
Lemma tree_echelon_s1 x:
  (treep x /\ tree_size x = \0c) ->  echelon_s1 (tree_to_echelon x).
Proof.
move => [ha hb].
by move:(tree_to_echelon_ok ha);rewrite hb succ_zero => - [ra [_ /nesym rb] rc].
Qed.

Lemma Echelon_ex1_prop1: echelon_s1 Echelon_ex1.
Proof. exact: (tree_echelon_s1 Tree_ex1_prop). Qed.

Lemma Echelon_ex2_prop1: echelon_s1 Echelon_ex2.
Proof. exact: (tree_echelon_s1 Tree_ex2_prop). Qed.

Lemma Echelon_ex3_prop1: echelon_s1 Echelon_ex3.
Proof. exact: (tree_echelon_s1 Tree_ex3_prop). Qed.

Lemma Echelon_value_ex1 E (A := Vg E \0c):
  echelon_of_base Echelon_ex1 E =  \Po (A \times A) /\
  echelon_can_extension Echelon_ex1 E =  \Pof (A \ftimes A). 
Proof.
move:(proj1 Tree_ex1_prop ) => xx.
move:(tree_value_prop E) => [ha hb hc].
move:(tree_extension_prop E) => [ha' hb' hc'].
move: (tdepth_prop_inv) => [qa qb qc].
move: (proj1 (qa _ NS0)) => ta.
move: (proj1 (qc _ _ ta ta)) => tb.
rewrite /Echelon_ex1  (echelon_of_base_of_tree E xx) /Tree_ex1.
 rewrite (hb _ tb) (hc _ _ ta ta) (ha _ NS0).
rewrite (can_extension_of_tree E xx).
by rewrite (hb' _ tb) (hc' _ _ ta ta) (ha' _ NS0).
Qed.



Lemma Echelon_value_ex2 E (A := Vg E \0c):
 echelon_of_base Echelon_ex2 E = \Po ((A \times A) \times A) /\
   echelon_can_extension Echelon_ex2 E = \Pof ((A \ftimes A) \ftimes A).
Proof.
move:(proj1 Tree_ex2_prop ) => xx.
move:(tree_value_prop E) => [ha hb hc].
move:(tree_extension_prop E) => [ha' hb' hc'].
move: (tdepth_prop_inv) => [qa qb qc].
move: (proj1 (qa _ NS0)) => ta.
move: (proj1 (qc _ _ ta ta)) => tb.
move: (proj1 (qc _ _ tb ta)) => tc.
rewrite /Echelon_ex2  (echelon_of_base_of_tree E xx) /Tree_ex2.
rewrite (hb _ tc) (hc _ _ tb ta)  (hc _ _ ta ta)  (ha _ NS0).
rewrite (can_extension_of_tree E xx).
by rewrite (hb' _ tc) (hc' _ _ tb ta)  (hc' _ _ ta ta)  (ha' _ NS0).
Qed.


Lemma Echelon_value_ex3 E (A := Vg E \0c):
  echelon_of_base Echelon_ex3 E = \Po (\Po A) /\
   echelon_can_extension Echelon_ex3 E = \Pof (\Pof A).
Proof.
move:(proj1 Tree_ex3_prop ) => xx.
move:(tree_value_prop E) => [ha hb hc].
move:(tree_extension_prop E) => [ha' hb' hc'].
move: (tdepth_prop_inv) => [qa qb qc].
move: (proj1 (qa _ NS0)) => ta.
move: (proj1 (qb _ ta)) => tb.
rewrite /Echelon_ex2  (echelon_of_base_of_tree E xx) /Tree_ex2.
rewrite (can_extension_of_tree E xx).
by rewrite (hb _ tb) (hb _ ta) (ha _ NS0) (hb' _ tb) (hb' _ ta) (ha' _ NS0).
Qed.






End Example2.


End Structure.
Export Structure.
