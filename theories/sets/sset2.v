(** * Theory of Sets  EII-3 Correspondences
  Copyright INRIA (2009-2013 2018) Apics; Marelle Team (Jose Grimm).
*)

(* $Id: sset2.v,v 1.8 2018/09/04 07:58:00 grimm Exp $ *)

From Coq Require Import Setoid.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
From gaia Require Export sset1.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** EII-3-1  Graphs et correspondences *)

Module Correspondence.

(** ** Additional lemmas *) 

(** Proposition 1: existence and uniqueness of range and domain *)

Theorem range_domain_exists r: sgraph r -> 
  ((exists! a, forall x, inc x a <-> (exists y, inc (J x y) r)) /\
    (exists! b, forall y, inc y b <-> (exists x, inc (J x y) r))).
Proof.
move=> gr; split; apply /unique_existence; split.
- exists (domain r) => t; apply/(domainP gr).
- by move=> x y Hx Hy; set_extens t; rewrite Hx Hy. 
- by exists (range r) => t;  apply/(rangeP gr).
- by move=> x y Hx Hy; set_extens t; rewrite Hx Hy. 
Qed. 


(** A product is a special graph *)

Lemma sub_graph_setX r: sgraph r -> 
  sub r ((domain r) \times (range r)).
Proof. move=> gr t tr; apply/setX_P; split; fprops.  Qed.

Lemma setX_graph x y: sgraph (x \times y).
Proof. by move=> t /setX_P []. Qed. 

Lemma sub_setX_graph u x y: sub u (x \times y) -> sgraph u.
Proof. move=> su t tu; exact: (setX_graph (su _ tu)). Qed. 

Hint Resolve setX_graph: fprops.

Lemma setX_relP x y a b:
  related (x \times y) a b <-> (inc a x /\ inc b y).
Proof.  
by split;[ move/setX_P => [_ ]; aw | move => [ax biy]; apply: setXp_i ].
Qed.

Lemma setX_domain x y: nonempty y -> domain (x \times y) = x.
Proof.  
move=> [z zy]; set_extens t. 
  by case/funI_P => u /setX_P [_ xx _] ->.
move=> tx; apply/funI_P;exists (J t z); aw; fprops. 
Qed.

Lemma setX_range x y: nonempty x -> range (x \times y) = y.
Proof.  
move=> [z zy]; set_extens t. 
  by case/(funI_P) => u /setX_P [_ _ xx] ->.
move=> tx; apply/funI_P;exists (J z t); aw; fprops. 
Qed.

(** Diagonal of a set: this is a functional graph [x -> x] *)

Definition diagonal x := Zo (coarse x)(fun y=> P y = Q y).

Lemma diagonal_i_P x u:
  inc u (diagonal x) <-> [/\ pairp u, inc (P u) x & P u = Q u].
Proof.
split; first by case/Zo_P => /setX_P [ta tb _] tc.
move=> [ta tb tc]; apply: Zo_i => //;rewrite -ta; apply: setXp_i => //; ue.
Qed.

Lemma diagonal_pi_P x u v:
  inc (J u v) (diagonal x) <-> (inc u x /\ u = v).
Proof.
apply: (iff_trans (diagonal_i_P x (J u v))); aw.
split; [by case | move => []; split; fprops ].
Qed.

Lemma diagonal_is_identity x: diagonal x = identity_g x.
Proof.
set_extens t.
  move /diagonal_i_P => [pt Pt eql]; rewrite -pt -eql;apply /funI_P; ex_tac.
by move /funI_P => [z zx ->]; apply/diagonal_pi_P.
Qed.


(** A correspondence is a triple (G,A,B), graph, source and target,  
   such that [G] is a subset of the product [A \times B].
   The domain of [G] is a subset of [A].
   The range of [G] is a subset of [B].
 *)

Definition triplep f := pairp f /\ pairp (Q f).
Definition source x := P (Q x). 
Definition target x := Q (Q x). 
Definition graph x := P x. 

Definition triple s t g  := J g (J s t).

Definition correspondence f  :=
  triplep f /\ sub (graph f) ((source f) \times (target f)).

Lemma corr_propcc s t g:
  sub g (s \times t) <-> [/\ sgraph g, sub (domain g) s & sub (range g) t].
Proof.  
split => [sg | [gg sd sr] x xg ].
  have gg:= (sub_setX_graph sg).
  by split =>// z /funI_P [y yp ->];move/setX_P: (sg _ yp) => [_].
rewrite -(gg _ xg); apply: setXp_i; [ apply: sd | apply: sr]; fprops.
Qed.

Lemma corr_propc f (g := graph f):
  correspondence f ->
  [/\ sgraph g, sub (domain g) (source f) & sub (range g) (target f)].
Proof. by move=> [tf sg]; apply /corr_propcc. Qed.

Lemma triple_corr s t g: triplep (triple s t g).
Proof. by rewrite /triple; split; [| aw]; fprops. Qed.

Lemma corresp_recov f: triplep f ->
  triple (source f) (target f) (graph f) = f.
Proof. 
by rewrite /triple /source /target /graph => [] [pf ->].
Qed.

Lemma corresp_recov1 f: correspondence f ->
  triple (source f) (target f) (graph f) = f.
Proof. by move => [t _]; apply: corresp_recov. Qed.

Lemma corresp_s s t g: source (triple s t g) = s.
Proof. by rewrite /triple /source; aw. Qed.

Lemma corresp_t s t g: target (triple s t g) = t.
Proof. by rewrite /triple /target; aw. Qed.

Lemma corresp_g  s t g: graph (triple s t g) = g.
Proof. by rewrite /triple /graph; aw. Qed.

Hint Rewrite corresp_s corresp_t corresp_g : aw.

Lemma corresp_create s t g:
  sub g (s \times t) -> correspondence (triple s t g).
Proof. by move=> h; split; [apply: triple_corr | aw ]. Qed.

(** Some properties of a correspondence *)

Lemma corresp_is_graph g: correspondence g -> sgraph (graph g).
Proof. by case/corr_propc. Qed.

Lemma corresp_sub_range g:
  correspondence g -> sub (range (graph g)) (target g).
Proof. by move /corr_propc => [_ _]. Qed.

Lemma corresp_sub_domain g:
  correspondence g -> sub (domain (graph g)) (source g).
Proof. by move /corr_propc => [_].  Qed.

Hint Resolve corresp_sub_range corresp_sub_domain corresp_is_graph: fprops.

(** The set of correspondences  [E->F] is the product of [P] and [singleton E] 
   and [singleton F], where [P == \Po (E \times F)] 
   is the set of graphs of correspondences *)

Definition correspondences x y :=
  (\Po (x \times y)) \times ( (singleton x) \times (singleton y)).

Lemma correspondences_P x y z:
  inc z (correspondences x y) <->
  [/\ correspondence z, source z = x & target z = y].
Proof. 
rewrite /correspondence /source/target.
split.
  by case/setX_P => [pz /setP_P spz/setX_P [p_qz /set1_P -> /set1_P ->]].
move => [ [ [tp sgp] aux] <- <-].
apply:setX_i;[ exact | by apply/ setP_P | apply:setX_i; fprops].
Qed.


(** Image by the graph [r] of a set [u] *)

Definition direct_image f X:=
  Zo (range f) (fun y=>exists2 x, inc x X & inc (J x y) f). 

Definition Vfs f := direct_image (graph f).
Definition Imf f := Vfs f (source f).

Lemma dirim_P f X y:
  inc y (direct_image f X) <-> exists2 x, inc x X & inc (J x y) f.
Proof. 
split => [ /Zo_hi // | [x xu pr]]; apply/Zo_i; ex_tac.
Qed.

Lemma dirimE f X: fgraph f -> sub X (domain f) ->
  direct_image f X = fun_image X (Vg f).
Proof.
move => sgf sxd; set_extens t.
  move /dirim_P => [x xX pf]; apply /funI_P.
  move: (pr2_V sgf pf); aw => ->; ex_tac.
move /funI_P => [z sX ->]; apply /dirim_P; ex_tac; apply: fdomain_pr1 => //.
by apply: sxd.
Qed.

Lemma dirim_Sr f X: sub (direct_image f X) (range f).
Proof. apply: Zo_S. Qed.

Lemma dirim_domain f: sgraph f -> direct_image f (domain f) =  range f.
Proof.
move=> sgf; apply: extensionality; first by apply: dirim_Sr.
move => t /funI_P [y yf ->]; apply: Zo_i; first by fprops.
by exists (P y); fprops;rewrite (sgf _ yf). 
Qed.

Lemma dirim_set0 f: direct_image f emptyset =  emptyset.
Proof. by apply /set0_P => t /Zo_hi [x /in_set0]. Qed.

Lemma dirim_setn0 f u: sgraph f -> nonempty u -> sub u (domain f)
  -> nonempty (direct_image f u).
Proof. 
move=> gr [x xu] udf; move: (udf _ xu); case /(domainP gr)=> [y Jr].
exists y;apply: Zo_i; ex_tac.
Qed.

Theorem dirim_S f: {compat (direct_image f): u v / sub u v}.
Proof. 
move=> u u' uu' t /dirim_P [x xu pr]; apply/dirim_P.
by exists x => //;apply: uu'.
Qed.

(** Section of the graph [r] at [x] *)

Definition im_of_singleton f x:= direct_image f (singleton x).

Lemma dirim_set1_P f x y:
  inc y (im_of_singleton f x) <-> inc (J x y) f.
Proof.
apply: (iff_trans (dirim_P f _ y)).
split; [ by move =>  [z /set1_P ->] | move => pf; ex_tac; fprops ].
Qed.

Lemma dirim_set1_S f f': sgraph f -> sgraph f' ->
  ((forall x, sub (im_of_singleton f x) (im_of_singleton f' x)) <-> sub f f').
Proof. 
move=> gr gr'; split=> s x t.
  move: (gr _ t) => eql; rewrite - eql;apply/dirim_set1_P.
  by apply: s; apply/dirim_set1_P; rewrite eql.
by move/dirim_set1_P => jf; apply/dirim_set1_P; apply:s.
Qed.

(** ** EII-3-2 Inverse of a correspondence  *)

(** Inverse graph of [r] *)

Definition inverse_graph r :=
  Zo ((range r) \times (domain r))  (fun y=> inc (J (Q y)(P y)) r).

Lemma igraph_graph r: sgraph (inverse_graph r).
Proof. move=> x /Zo_S xp; apply: (setX_pair xp). Qed.

Hint Resolve igraph_graph: fprops.

Lemma igraphP r y: 
  inc y (inverse_graph r) <-> (pairp y /\  inc (J (Q y)(P y)) r).
Proof. 
split; first by case/Zo_P => yp pr; split => //; apply: (setX_pair yp).
move => [py pr]; exact:(Zo_i (setX_i py (range_i pr) (domain_i pr)) pr). 
Qed.

Lemma igraph_pP r x y: inc (J x y) (inverse_graph r) <-> inc (J y x) r.
Proof. 
by split; [case/igraphP;aw | move=> pr; apply/igraphP; aw; fprops ].
Qed.

Lemma igraph_alt r: sgraph r ->
  inverse_graph r = fun_image r (fun z => J (Q z) (P z)).
Proof. 
move=> gr; set_extens t. 
  by move /igraphP => [pt h];apply/funI_P; ex_tac; aw; rewrite pt.
by move /funI_P => [c zr ->]; apply/igraph_pP; rewrite (gr _ zr).
Qed.

Lemma igraph_involutive : {when sgraph, involutive inverse_graph}.
Proof. 
move=> f gr; set_extens x;first by case/igraphP => px /igraph_pP; rewrite px.
move => xf; have px:= (gr _ xf).
by rewrite -px;apply/igraph_pP /igraph_pP; rewrite px.
Qed.

Lemma igraph_range r: sgraph r -> range (inverse_graph r) = domain r.
Proof. 
move=> gr; set_extens x; first by move/funI_P => [y /igraphP [_ h] ->]; ex_tac.
move/funI_P => [y yi ->]; apply: (range_i (x:=(Q y))); apply/igraph_pP.
by rewrite (gr _  yi).
Qed.

Lemma igraph_domain r: sgraph r ->  domain (inverse_graph r) = range r.
Proof. 
move=> gr;rewrite - {2} (igraph_involutive gr) igraph_range //.
apply: igraph_graph.
Qed.

Lemma igraph0: inverse_graph (emptyset) = emptyset.
Proof. by apply /set0_P => t /igraphP [_ /in_set0]. Qed.

Hint Rewrite igraph0: aw.

Lemma igraphX x y: inverse_graph (x \times y) =  y \times x.
Proof. 
set_extens t. 
  by move /igraphP => [pt /setX_P]; aw; move => [_ pa pb];apply: setX_i.
move/setX_P=> [pt pa pb]; apply /igraphP; fprops.
Qed.

Lemma igraph_identity_g x:
  inverse_graph (identity_g x) = identity_g x.
Proof.
rewrite/inverse_graph identity_r identity_d - diagonal_is_identity.
set_extens z;move /Zo_P => [pa pb]; apply: Zo_i => //.
  by move/Zo_hi: pb; aw.
by rewrite -pb;apply/diagonal_pi_P;split => //; move /setX_P: pa => [_].
Qed.

(** Inverse correspondence *)

Definition inverse_fun m :=
  triple (target m) (source m) (inverse_graph (graph m)).

Lemma icor_correspondence m:
  correspondence m -> correspondence (inverse_fun m).
Proof. 
move => [_ pb]; apply: corresp_create => x/igraphP [px pg]. 
by move /setXp_P: (pb _ pg) => [pc pd]; apply: setX_i.
Qed.

Lemma icor_involutive:
  {when correspondence, involutive inverse_fun}.
Proof. 
move=> m cm; rewrite /inverse_fun; aw; rewrite igraph_involutive;fprops.
by apply: corresp_recov1. 
Qed.

Lemma ifun_s f: source (inverse_fun f) = target f.
Proof. by rewrite/inverse_fun; aw. Qed.

Lemma ifun_t f: target (inverse_fun f) = source f.
Proof. by rewrite/inverse_fun; aw. Qed.

Lemma ifun_g f: graph (inverse_fun f) = inverse_graph (graph f).
Proof. by rewrite /inverse_fun;aw. Qed.

Hint Rewrite ifun_s ifun_t ifun_g : aw.
Hint Resolve icor_correspondence: fprops.

(** Inverse image by a graph r of a set x *)

Definition inverse_image r :=  direct_image (inverse_graph r).
Definition Vfi f:=  inverse_image (graph f).
Definition Vfi1 f x := Vfi f (singleton x).

Lemma iim_fun_pr r: Vfi r = Vfs (inverse_fun r).
Proof. by rewrite /Vfi /inverse_fun /Vfs; aw. Qed.

Lemma iim_graph_P x r y:
  (inc y (inverse_image r x)) <-> (exists2 u, inc u x & inc (J y u) r).
Proof. 
by apply: (iff_trans (dirim_P _ x y)); split; 
   move => [u ux pr]; ex_tac; apply /igraph_pP.
Qed.

Lemma iim_fun_P x r y: 
  inc y (Vfi r x) <-> (exists2 u, inc u x & inc (J y u) (graph r)).
Proof. exact:iim_graph_P. Qed.


(** ** EII-3-3  Composition of two correspondences *) 

(** Composition of two graphs *)

Definition composeg r' r :=
  Zo ((domain r) \times (range r'))
  (fun w => exists2 y, inc (J (P w) y) r & inc (J y (Q w)) r').
 
Notation "x \cg y" := (composeg x y) (at level 50).

Lemma compg_graph r r': sgraph (r \cg r').
Proof. by move=> t /Zo_P [/setX_pair]. Qed. 

Hint Resolve compg_graph: fprops.

Lemma compg_P r r' x:
  inc x (r' \cg r) <->
  (pairp x /\ (exists2 y, inc (J (P x) y) r & inc (J y (Q x)) r')).
Proof.
split;first by move/Zo_P => [pa pb];split => //; apply: (setX_pair pa).
move => [pa pb]; apply: Zo_i => //. 
move: pb => [z pc pd];apply/setX_P;split => //; ex_tac.
Qed. 

Lemma compg_pP r r' x y:
  inc (J x y) (r' \cg r) <-> (exists2 z, inc (J x z) r & inc (J z y) r').
Proof.
apply: (iff_trans (compg_P _ _ _) ); aw.
split;[ by case | move => h; fprops].
Qed.

Lemma compg_domain_S r r': sub (domain (r' \cg r)) (domain r).
Proof. move => t /funI_P [y /compg_P [_ [s sa _]] ->]; ex_tac. Qed.

Lemma compg_rangeS r r':  sub (range (r' \cg r)) (range r').
Proof. move => t /funI_P [y /compg_P [_ [s _ sa]] ->]; ex_tac. Qed.

Lemma compg_composef f g: f \cfP g -> f \cf g =  f \cg g.
Proof.
move => [fgf fgg srd].
set_extens t.
  move /funI_P => [z zd ->]; apply /compg_pP.
  exists (Vg g z); apply: fdomain_pr1 => //; apply: srd.
  apply /range_gP => //; ex_tac.
move/compg_P => [pt [y Pt Qt]]; apply /funI_P; exists (P t); first by ex_tac.
by move: (pr2_V fgg Pt)(pr2_V fgf Qt); aw => <- <-. 
Qed.


(** Proposition 3, inverse of composition *)

Theorem compg_inverse: {morph inverse_graph : a b / a \cg b >-> b \cg a}.
Proof.
move => r r';set_extens x. 
  move/igraphP => [px] /compg_pP [z pa pb].
  by rewrite -px; apply/compg_pP; exists z => //; apply/igraph_pP.
move/compg_P => [px [y /igraph_pP pa /igraph_pP pb]]. 
by rewrite -px; apply/igraph_pP/compg_pP; exists y.
Qed.

(** Proposition 4,  associativity of composition *)

Theorem compgA : associative composeg.
Proof.
move => r r' r'';set_extens x.
  move /compg_P=> [px [y /compg_pP [z pa pb] pc]].
  rewrite -px; apply/compg_pP; ex_tac; apply/compg_pP; ex_tac.
move /compg_P=> [px [y pa /compg_pP [z pb pc]]].
rewrite -px; apply/compg_pP; ex_tac; apply/compg_pP; ex_tac.
Qed.

(** Proposition 5 Image of composition *)

Theorem compg_image: action_prop direct_image composeg.
Proof. 
move => gr_imegr' r x;set_extens t.
  move /dirim_P => [z zx /compg_pP [u pa pb]].
  apply/dirim_P; ex_tac; apply/dirim_P; ex_tac.
move /dirim_P => [z /dirim_P [u pa pb] pc].
apply/dirim_P; ex_tac; apply/compg_pP; ex_tac.
Qed.

(** More properties of composition *)

Lemma compg_domain r r':
  sgraph r' -> domain (r' \cg r) = inverse_image r (domain r').
Proof. 
move=>gr; have cg:= (@compg_graph r' r); set_extens t.
  move/(domainP cg) => [y /compg_pP [z pa pb]].
  apply/iim_graph_P; ex_tac; ex_tac.
move/iim_graph_P => [x /(domainP gr) [y pa] pb].
apply/(domainP cg); exists y; apply /compg_pP; ex_tac.
Qed.

Lemma compg_range r r':
  sgraph r -> range (r' \cg r) = direct_image r' (range r).
Proof.
move=>gr;have cg:= (@compg_graph r' r); set_extens t.
  move/(rangeP cg) => [y /compg_pP [z pa pb]]; apply/dirim_P; ex_tac; ex_tac.
move/dirim_P => [x /(rangeP gr) [y pa] pb].
apply/(rangeP cg); exists y; apply /compg_pP; ex_tac.
Qed.

Lemma inverse_direct_imageg r x:
  sgraph r -> sub x (domain r) ->
  sub x (inverse_image r (direct_image r x)).
Proof. 
move=> gt xd t tx.
move /funI_P: (xd _ tx)=> [y yr eq].
have aux:inc (J t (Q y)) r by rewrite eq (gt _ yr).
apply/iim_graph_P;ex_tac;apply/dirim_P; ex_tac.
Qed.

Lemma compg_S r r' s s':
  sub r s -> sub r' s' -> sub (r' \cg r) (s' \cg s).
Proof. 
move=> rs rs' t /compg_P [ {3} <- [ x ir ir']].
by apply/compg_pP; exists x; [apply: rs | apply: rs'].
Qed.

(** Composition of two correspondences *)

Definition composableC r' r := 
  [/\ correspondence r, correspondence r' & source r' = target r].
Definition compose r' r :=
  triple (source r)(target r') ((graph r') \cg (graph r)).

Notation "f1 \co f2" := (compose f1 f2) (at level 50).

Lemma compf_correspondence r' r:
  correspondence r -> correspondence r' -> 
  correspondence (r' \co r).
Proof.  
rewrite/compose=> cr cr'; apply: corresp_create.
move=>t /compg_P [pt [y ir ir']]; apply:setX_i => //.
  by move /setX_P: ((proj2 cr) _ ir) => [_ pa _];move: pa; aw.
by move /setX_P: ((proj2 cr') _ ir');aw; move => [_ _ pb]; move: pb; aw.
Qed.

Lemma compf_image: action_prop Vfs compose.
Proof. by move => r' r x; rewrite /Vfs -compg_image /compose; aw. Qed.

Lemma compf_inverse: {morph inverse_fun : a b / a \co b >-> b \co a}.
Proof.
by move=> a b; rewrite /inverse_fun /compose; aw; rewrite compg_inverse.
Qed.

(** Identity correspondence, will be shown to be a function later *)

Definition identity x := triple x x (identity_g x). 

Lemma identity_corresp x: correspondence (identity x).
Proof. 
by apply: corresp_create; rewrite -diagonal_is_identity; apply: Zo_S.
Qed.

Lemma identity_s x: source (identity x) = x.
Proof. by rewrite/identity; aw. Qed.

Lemma identity_t x: target (identity x) = x.
Proof. by rewrite/identity; aw.  Qed. 

Lemma identity_graph0 x: graph (identity x) = identity_g x.
Proof. by rewrite/identity; aw.  Qed. 

Hint Rewrite identity_s identity_t: aw.

Lemma compf_id_left m:
   correspondence m -> (identity (target m)) \co m = m.
Proof. 
move=> cm.
suff : ((identity_g (target m)) \cg (graph m) = graph m).
  by rewrite /compose identity_graph0; aw => ->; apply: corresp_recov1.
rewrite -diagonal_is_identity.
set_extens t.
  by move /compg_P=> [ {3} <- [y p1 /diagonal_pi_P [_ <-]]].
have gm: (sgraph (graph m)) by fprops.
move => tg; apply/compg_P; split; first by apply: (gm _ tg).
move /setX_P: ((proj2 cm) _ tg) => [pt _ qt].
by exists (Q t); [ rewrite pt | apply/diagonal_pi_P].
Qed. 

Corollary compose_identity_left E:
  {when (fun x => correspondence x /\ (target x) = E),
  left_id (identity E) compose}.
Proof. move => x [cx <-]; exact:compf_id_left. Qed.

Lemma compf_id_right m:
  correspondence m -> m \co (identity (source m)) = m.
Proof. 
move=> cm.
suff: ((graph m) \cg (identity_g (source m))= graph m).
  by rewrite /compose identity_graph0; aw => ->; apply: corresp_recov1.
rewrite -diagonal_is_identity.
set_extens t.
  by move /compg_P => [ {3} <- [y /diagonal_pi_P [pa ->] p1]].
have gm: (sgraph (graph m)) by fprops.
move => tg; apply/compg_P; split; first by apply: (gm _ tg).
move /setX_P: (proj2 cm _ tg) => [pt qt _].
by exists (P t); [ apply/diagonal_pi_P | rewrite pt ].
Qed.

Lemma compf_id_id x: 
  (identity x) \co (identity x) =  (identity x).
Proof. by move: (compf_id_right (@identity_corresp x)); aw. Qed.

Lemma identity_self_inverse x: 
  inverse_fun (identity x) =  (identity x).
Proof. by rewrite /inverse_fun /identity; aw;  rewrite igraph_identity_g. Qed.



End Correspondence.

Export Correspondence.

(** **  EII-3-4 Functions*)
Module Bfunction.

Import Correspondence.

(** This is a different but equivalent definition *)

Definition functional_graph r := forall x, singl_val (related r x).

Lemma functionalP r:
  (sgraph r /\ functional_graph r) <-> (fgraph r).
Proof. 
rewrite /functional_graph /related; split; last first.
  by move=> fr; split; fprops; move=> x y y'; apply: fgraph_pr.
move => [gr eql]; split=>// x y xr yr eqp.
move: (xr) (yr); rewrite -(gr _ xr) - (gr _ yr) -eqp => pa pb.
by rewrite (eql _ _ _ pa pb).
Qed.

(** A function is a correspondence with a functional graph whose
   source is the domain of the graph *)

Definition function f :=
  [/\ correspondence f, fgraph (graph f) & source f = domain (graph f)].

Lemma function_pr s t g:
  fgraph g -> sub (range g) t -> s = domain g ->
  function (triple s t g).
Proof. 
rewrite /function => fg sr d; aw; split => //.
by apply: corresp_create; rewrite d; apply /corr_propcc; split => //;case: fg.
Qed.

Lemma function_fgraph f: function f -> fgraph (graph f).
Proof. by move=> [_]. Qed.

Lemma function_sgraph f: function f -> sgraph (graph f).
Proof. by move=> [_ [h _]]. Qed.

Lemma domain_fg f: function f -> domain (graph f) = source f.
Proof. by move=> [_ ]. Qed.

Lemma f_range_graph f: function f -> sub (range (graph f))(target f).
Proof. by move => [cf _ _]; apply:corresp_sub_range. Qed.

Hint Resolve function_sgraph function_fgraph : fprops.

Lemma ImfE f: function f -> Imf f =  range (graph f).
Proof.
move=> ff; rewrite /Imf -domain_fg //.
by apply: dirim_domain; fprops.
Qed.


(** The value of the function [f] at [x] is [Vf x f] *)

Definition Vf f x := Vg (graph f) x.

Section Vf_pr.
Variable  f: Set.
Hypothesis ff: function f.

Lemma Vf_pr3 x: inc x (source f) -> inc (J x (Vf f x)) (graph f).
Proof. by move=> xf; apply: fdomain_pr1; fprops; rewrite domain_fg. Qed.

Lemma in_graph_Vf x: inc x (graph f) -> x = (J (P x) (Vf f (P x))).
Proof. by move=> xf; apply: in_graph_V; fprops. Qed.

Lemma Vf_pr2 x: inc x (graph f) -> Q x = Vf f (P x).
Proof. by move=> xg; apply: pr2_V; fprops. Qed.

Lemma Vf_pr x y: inc (J x y) (graph f) -> y = Vf f x.
Proof. by move=> Jg; move: (in_graph_Vf Jg); aw; apply: pr2_def. Qed.

Lemma range_fP y: 
  inc y (range (graph f)) <-> exists2 x, inc x (source f) & y = Vf f x.
Proof. move: ff => [_ fgf ->]; apply/(range_gP fgf). Qed.

Lemma Vf_range_g x: inc x (source f) -> inc (Vf f x) (range (graph f)).
Proof. move=> xsf; apply /range_fP;ex_tac.  Qed.

Lemma Vf_target x: inc x (source f) -> inc (Vf f x) (target f).
Proof. move/Vf_range_g;apply: (f_range_graph ff).
Qed.

Lemma p1graph_source x y: inc (J x y) (graph f) -> inc x (source f).
Proof. move: ff => [_ fgf ->] jg; ex_tac. Qed.

Lemma p2graph_target x y : inc (J x y) (graph f) -> inc y (target f).
Proof.
move=> Jgf; rewrite (Vf_pr Jgf); apply: Vf_target; apply: (p1graph_source Jgf).
Qed.

Lemma p1graph_source1 x: inc x (graph f) -> inc (P x) (source f).
Proof. 
move=> xgf; apply: (p1graph_source (y:= (Vf f (P x)))).
by rewrite - (in_graph_Vf xgf).
Qed.

Lemma p2graph_target1 x: inc x (graph f) -> inc (Q x) (target f).
Proof.
move=> xgf; rewrite (in_graph_Vf xgf); aw. 
by apply: Vf_target => //; apply: p1graph_source1.
Qed.


Lemma Vf_image_P x: sub x (source f) -> forall y,
  (inc y (Vfs f x) <-> exists2 u, inc u x & y = Vf f u).
Proof. 
rewrite /Vfs => ss;split.
  by move/dirim_P => [a ax Jg]; ex_tac; apply: Vf_pr.
move=> [u ux ->]; apply/dirim_P; ex_tac;apply: Vf_pr3; fprops.
Qed.

Lemma Imf_P y:
  inc y (Imf f)  <-> (exists2 u, inc u (source f) & y = Vf f u).
Proof. exact: (Vf_image_P (@sub_refl (source f))). Qed.

Lemma fun_image_Starget1 x: sub (Vfs f x) (target f).
Proof. apply: sub_trans (f_range_graph ff); apply: dirim_Sr. Qed.

Lemma Imf_Starget: sub (Imf f) (target f).
Proof. apply: fun_image_Starget1. Qed.

End Vf_pr.

Hint Resolve Vf_target : fprops.

Lemma Imf_i f x: function f -> inc x (source f) -> inc (Vf f x) (Imf f).
Proof. move => ff xsf; apply/(Imf_P ff); ex_tac. Qed.

Ltac Wtac :=
  match goal with
    | |-  inc (J ?x (Vf ?f ?x)) (graph ?f) => apply: Vf_pr3 ; fprops
    |  h:inc (J ?x ?y) (graph ?f) |- Vf ?f ?x = ?y 
       => symmetry; apply: Vf_pr ; fprops
    |  h:inc (J ?x ?y) (graph ?f) |- ?y  = Vf ?f ?x => apply: Vf_pr ; fprops
    | |- inc (Vf ?f _) (range (graph ?f)) => apply: Vf_range_g ; fprops
    | |- inc (Vf ?f _) (Imf ?f) => apply: Imf_i ; fprops
    | h1: function ?f, h2: inc ?x (source ?f) |- inc (Vf ?f ?x) (target ?f)  
        => apply: (Vf_target h1 h2)
    | h2:target ?f = ?y |- inc (Vf ?f ?x) ?y 
        =>  rewrite - h2; Wtac
    | h2: ?y = target ?f  |- inc (Vf ?f ?x) ?y 
      =>  rewrite  h2; Wtac
    | h1: inc ?x ?y,  h2: ?y = source ?f |- inc (Vf ?f ?x) (target ?f)  
      =>  rewrite h2 in h1; Wtac
    | h1: inc ?x ?y,  h2: source ?f = ?y |- inc (Vf ?f ?x) (target ?f)  
      => rewrite - h2 in h1; Wtac
    | |- inc (Vf ?f _) (target ?f)  
        => apply: (Vf_target); fprops
    | Ha:function ?X1, Hb: inc (J _ ?X2) (graph ?X1)
      |-  inc ?X2 (target ?X1)
        => apply: (p2graph_target Ha Hb)
    | Ha:function ?X1, Hb: inc (J ?X2 _) (graph ?X1)
      |-  inc ?X2 (source ?X1)
        => apply: (p1graph_source Ha Hb)
    | Ha:function ?X1, Hb: inc ?X2 (graph ?X1)
      |-  inc (P ?X2) (source ?X1)
        => apply: (p1graph_source1 Ha Hb)
    | Ha:function ?X1, Hb: inc ?X2 (graph ?X1)
      |-  inc (Q ?X2) (target ?X1)
        => apply: (p2graph_target1 Ha Hb)
  end.

Lemma function_functional f: correspondence f ->
  (function f <-> (forall x, inc x (source f) -> 
    exists! y, related (graph f) x y)).
Proof.
rewrite/related=> cf; split. 
  move=> ff x xsf;exists (Vf f x); split; first by Wtac.
  move => y yg; symmetry; apply: (Vf_pr ff yg).
move => eu.
have sd:source f = domain (graph f).
  apply: extensionality; last by fprops.
  move=> t ts; move: (eu _ ts) => [y [ja jb]]. 
  by apply/funI_P; ex_tac; aw.
split=>//;apply /functionalP; split; first by fprops.
move=> x y y'; rewrite /related => h1.
have isf: inc x (source f) by rewrite sd; apply/funI_P; ex_tac; aw.
move: h1; move/unique_existence: (eu _ isf) => [_]; apply.
Qed.

(** Lemmas that say when two functions are equal *)

Definition same_Vf  f g:= Vf f =1 Vf g.
Definition cstfp (f E: Set) := singl_val_fp (inc ^~E) (Vf f).
Definition cstgp (f E: Set) := singl_val_fp (inc ^~E) (Vg f).


Notation "f1 =1f f2" := (same_Vf f1 f2)
  (at level 70, no associativity) : type_scope.

Lemma function_exten3 f g:
  function f -> function g ->
  graph f = graph g -> target f = target g -> source f = source g -> 
  f = g.
Proof. 
move => [[ff _] _ _]  [[fg _] _ _] e1 e2 e3.
by rewrite -(corresp_recov ff) -(corresp_recov fg); congr (triple _ _ _).
Qed.

Lemma function_exten1 f g:
  function f -> function g -> 
  graph f = graph g -> target f = target g -> 
  f = g.
Proof. 
move => ff fg e1 e2; apply: function_exten3=>//. 
by rewrite -!domain_fg // e1.
Qed.

Lemma function_exten f g:
  function f -> function g -> 
  source f = source g -> target f = target g ->  {inc (source f), f =1f g} ->
  f = g.
Proof.
move=> ff fg e1 r2 e2; apply: function_exten3=> //. 
set_extens x => xg.
  have Pf : (inc (P x) (source f)) by Wtac. 
  by rewrite (in_graph_Vf ff xg) (e2 _ Pf);  Wtac; rewrite -e1.
have Pg : (inc (P x) (source f)) by rewrite e1; Wtac. 
by rewrite (in_graph_Vf fg xg) -(e2 _ Pg);  Wtac. 
Qed. 

(** The image of singleton by a function is a singleton*)

Lemma fun_image_set1 f x:
  function f -> inc x (source f) ->
  Vfs f (singleton x) = singleton (Vf f x).
Proof. 
move=> ff xsf.
apply: set1_pr; first by apply /dirim_set1_P; Wtac.
by move => z /dirim_set1_P jg; apply:Vf_pr.
Qed.

Lemma fun_image_set0 f: Vfs f emptyset = emptyset.
Proof. by apply /set0_P => t /Zo_hi [x /in_set0]. Qed.

Lemma iim_fun_C g x:
  function g ->
  Vfi g ((target g) -s x) = (source g) -s (Vfi g x).
Proof.
move => fg. 
have gg: sgraph (graph g) by fprops.
set_extens t. 
  move/iim_graph_P => [u /setC_P [ut nux] Jug];apply/setC_P. 
  split; first by Wtac.
  move/iim_graph_P => [w wx Jwg].
  by case: nux; rewrite (fgraph_pr (proj32 fg) Jug Jwg).
move/setC_P =>  [ts neu].
have Jg: (inc (J t (Vf g t))(graph g)) by Wtac.
apply/iim_graph_P; ex_tac;apply/setC_P; split; fprops.
dneg Wx; apply/iim_graph_P; ex_tac.
Qed.

Lemma iim_fun_set1_hi f x y: function f ->
   inc x (Vfi1 f y) -> y = Vf f x.
Proof. by move => ff /iim_fun_P [u /set1_P ->]; apply: Vf_pr. Qed.

Lemma iim_fun_set1_i f x y: function f -> inc x (source f) ->
  y = Vf f x -> inc x (Vfi1 f y).
Proof. move => ff xsf ->; apply /iim_fun_P; ex_tac; Wtac. Qed.

Lemma iim_fun_set1_P f y: function f -> forall x,
   inc x (Vfi1 f y) <-> 
   (inc x (source f) /\ y = Vf f x).
Proof. 
move => ff x; split.
  move /iim_fun_P => [u /set1_P -> pa]; split;Wtac.
by move => [pa pb]; apply:iim_fun_set1_i.
Qed.

Lemma iim_fun_set1_E f y: function f ->
   (Vfi1 f y) = Zo (source f) (fun x => y = Vf f x).
Proof.
move => ff; set_extens t.
  by move /(iim_fun_set1_P _ ff) => pa; apply /Zo_P.
by move => /Zo_P pa; apply /(iim_fun_set1_P _ ff).
Qed.



Definition function_prop f s t:= 
  [/\ function f, source f = s & target f = t]. 

(** Function with empty graph *)

Definition empty_function_tg (x: Set) :=  triple emptyset x emptyset.
Definition empty_function:= empty_function_tg emptyset.

Lemma empty_function_tg_function x: 
  function_prop (empty_function_tg x) emptyset x.
Proof.
hnf; rewrite /empty_function_tg; aw; split => //; apply: function_pr; aww.
apply: fgraph_set0.
Qed.

Lemma empty_function_function: function_prop empty_function emptyset emptyset.
Proof. apply:empty_function_tg_function. Qed.

Lemma empty_function_graph x: graph (empty_function_tg x) = emptyset.
Proof. by rewrite /empty_function_tg; aw. Qed.

Lemma empty_function_p1 f: function f ->
  graph f = emptyset -> source f = emptyset.
Proof. by move => [_ _ ->] ->; aw. Qed.

Lemma empty_function_p2 f: function f ->
  target f = emptyset -> source f = emptyset.
Proof. 
by move => ff te; apply /set0_P => x /(Vf_target ff); rewrite te => /in_set0. 
Qed.

Lemma empty_source_graph f:
  function f -> source f = emptyset -> graph f = emptyset.
Proof. 
move => ff sfe; apply /set0_P => x xp.
apply: (@in_set0 (P x)); rewrite - sfe; Wtac.
Qed. 

Lemma empty_target_graph f:
  function f -> target f = emptyset -> graph f = emptyset.
Proof.
move => ff sfe; apply /set0_P => x xp. 
case: (@in_set0 (Vf f (P x))); Wtac; Wtac.
Qed.

Lemma empty_source_graph2 f:
  function f -> source f = emptyset -> 
  f =  empty_function_tg (target f).
Proof. 
move => pa pb;have pc:= (empty_source_graph pa pb).
by rewrite /empty_function_tg -{1} (corresp_recov (proj1 (proj31 pa))) pb pc.
Qed. 

(** Properties of the identity function *)

Lemma identity_prop x: function_prop (identity x) x x.
Proof.
rewrite /identity /function_prop; aw; split => //; apply: function_pr.
- by apply: identity_fgraph. 
- by rewrite identity_r; fprops. 
- by rewrite identity_d.
Qed.

Lemma identity_f x: function (identity x).
Proof. exact: (proj31 (identity_prop x)). Qed.

Lemma idV x y: inc y x -> Vf (identity x) y = y.
Proof. move =>yx; rewrite /Vf /identity; aw; apply:(identity_ev yx). Qed.

Hint Resolve identity_f: fprops.
Hint Rewrite idV : bw.

Lemma identity_prop0 E f:
  function_prop f E E -> (forall x, inc x E -> (Vf f x) = x) ->
  f = identity E.
Proof.
move: (identity_prop E) =>  [fa sa ta] [fb sb tb] fv.
apply:function_exten => //; try ue.
by rewrite sb => x xE; bw =>//; apply: fv.
Qed.



(** ** EII-3-5 Restrictions and extensions of functions *) 

(**  The functions agree on [x] if they take the same value *)
Definition agrees_on x f f' :=
  [/\ sub x (source f), sub x (source f') & {inc x, f =1f f'} ].

Lemma same_graph_agrees f f':
  function f -> function f' -> graph f = graph f' ->
  agrees_on (source f) f f'.
Proof. 
move=> ff ff' geq. 
have seq: (source f = source f'). 
  by rewrite -(domain_fg ff) -(domain_fg ff') geq.
rewrite /agrees_on - seq; split; fprops.
move=> a /(Vf_pr3 ff); rewrite geq => aux.
by rewrite -(Vf_pr ff' aux). 
Qed.

Lemma function_exten2 f f':
  function f -> function f' ->
  (f = f' <-> 
   [/\ source f = source f', target f = target f' & agrees_on (source f) f f']).
Proof. 
move=> ff ff'; split. 
  by  move ->;split => //; split.
move => [seq teq [_ _ ag]]; apply: function_exten; fprops. 
Qed.

Lemma sub_functionP f g:
  function f -> function g -> 
  (sub (graph f) (graph g) <-> agrees_on (source f) f g).
Proof. 
move=> ff fg; split => hyp.
  split => //.
    by do 2 rewrite -domain_fg=>//; apply: domain_S.  
  by move=> a af /=;rewrite- (Vf_pr fg (hyp _ (Vf_pr3 ff af))).
move => t tg; move: hyp => [_ sg ag].
have Ptsf: (inc (P t) (source f)) by Wtac.
rewrite (in_graph_Vf ff tg) (ag _ Ptsf);  Wtac. 
Qed.

(** Restriction of the function to a part of it source *)

Lemma restr_range f x:
  function f -> sub x (source f) -> 
  sub (range (restr (graph f) x)) (target f).
Proof. 
move=> ff sxdf t /funI_P [z /funI_P [s zg ->] ->]; aw;rewrite -/(Vf _ _); Wtac. 
Qed.

Definition restriction f x :=
  triple x (target f) (restr (graph f) x).

Definition restriction1 f x :=
  triple x (Vfs f x) (restr (graph f) x).

Definition restriction2 f x y := 
  triple x y ((graph f)\cap (x \times (target f))).

Definition restriction2_axioms f x y :=
  [/\ function f,
  sub x (source f), sub y (target f) & sub (Vfs f x) y].

Lemma restriction_prop f x:
  function f -> sub x (source f) ->
  function_prop (restriction f x) x (target f).
Proof.
rewrite /restriction /function_prop=> ff xs; aw; split => //. 
by apply: function_pr; aw; fprops; apply: restr_range.
Qed.

Lemma restriction1_prop f x:
  function f -> sub x (source f) ->
  function_prop (restriction1 f x) x (Vfs f x).
Proof.
rewrite /restriction1 /function_prop =>ff ssf; aw; split => //.
apply: function_pr; aww.
rewrite Lg_range => t /funI_P [z zx  ->]; apply/dirim_P; ex_tac.
rewrite -/(Vf _ _); Wtac.
Qed.

Lemma restriction2_props f x y:
  restriction2_axioms f x y ->
  domain ((graph f) \cap (x \times (target f))) = x.
Proof. 
move=> [ff xsf ysf etc]; set_extens t.
  by move/funI_P => [z /setI2_P [_ /setX_P [_ h _]] ->].
move => tx; apply /domainP.
  by move => u /setI2_P [_] /setX_P [].
exists (Vf f t); apply/setI2_P; split; [Wtac| apply: setXp_i => //; Wtac].
Qed.

Lemma restriction2_prop f x y:
  restriction2_axioms f x y -> function_prop (restriction2 f x y) x y.
Proof. 
move=> ra; move:(ra) => [ff ss st etc].
rewrite /restriction2 /function_prop; aw; split => //.
move:(restriction2_props ra); set g :=  _ \cap _  => dg.
have fg: fgraph g.
  rewrite /g; apply: (@sub_fgraph _ (graph f)); fprops; apply: setI2_1.
apply: function_pr=>// t tr; apply: etc; apply /dirim_P.
move/(rangeP (proj1 fg)): tr => [z /setI2_P [jg /setXp_P [zx _]]];ex_tac.
Qed.

Lemma restriction_V f x:
  function f -> sub x (source f) ->
  {inc x, (restriction f x) =1f f}.
Proof. by rewrite /Vf/restriction => ff ss a xa; aw; rewrite LgV.  Qed.

Lemma restriction1_V f x:
  function f -> sub x (source f) ->
  {inc x, (restriction1 f x) =1f f}.
Proof. by rewrite /Vf/restriction1 => ff ss a xa; aw; rewrite LgV.  Qed.

Lemma restriction2_V f x y:
  restriction2_axioms f x y ->
  {inc x, (restriction2 f x y) =1f f}.
Proof. 
move => ra a ax; move: (ra) => [ff sf tf sif].
rewrite /Vf/restriction2; aw.
apply: sub_graph_ev; fprops;first by apply: setI2_1.
by rewrite (restriction2_props ra).
Qed.

Lemma restriction1_pr f:
  function f -> restriction2 f (source f) (Imf f) =
  restriction1 f (source f).
Proof. 
rewrite/restriction2/restriction1=> ff. 
have ->: (restr (graph f) (source f) = graph f).
  rewrite (proj33 ff); apply: restr_to_domain; fprops.
by rewrite (proj1 (setI2id_Pl _ _) (proj2 (proj31 ff))).
Qed.

(** [g] extends [f] if its restriction to the source of [f] is [f] *)

Definition extends g f := 
  [/\ function f, function g,  sub (graph f) (graph g)
    & sub (target f)(target g) ].

Lemma extends_Ssource f g:
  extends g f -> sub (source f) (source g).
Proof.
by move=> [ff fg sg st]; do 2 rewrite -domain_fg=>//; apply: domain_S.
Qed.

Lemma extends_sV f g:
  extends g f -> {inc (source f), f =1f g}.
Proof.
move=> ext x xf; have ss:= (extends_Ssource ext).
have [ff fg sg _] := ext.
have pg:  (inc (J x (Vf f x)) (graph g)) by apply: sg; Wtac. 
by rewrite (Vf_pr fg pg).
Qed.

Lemma function_extends_restr f x:
  function f -> sub x (source f) ->
  extends f (restriction f x).
Proof.
move =>ff ssf; have [pa pb pc] := (restriction_prop ff ssf).
split => //; last by rewrite pc.
rewrite /restriction; aw => s /funI_P [z zx ->]. 
by apply: Vf_pr3 => //; apply: ssf.
Qed.

Lemma agrees_same_restriction f g x:
  function f -> function g -> agrees_on x f g ->
  target f = target g -> 
  restriction f x =
  restriction g x.
Proof.
move=> ff fg [sf sg vfg] t.
move:(restriction_prop ff sf)(restriction_prop fg sg)=>[pa pb pc][pd pe pf].
rewrite/restriction; apply:function_exten;aww => z zs.
by do 2 rewrite restriction_V => //; apply: vfg.
Qed.

Lemma restriction_graph1 f x:
  function f -> sub x (source f) ->
  graph (restriction f x) =  (graph f) \cap (x \times (target f)).
Proof. 
rewrite /restriction => ff xs; aw;set_extens t; last first.
  move/setI2_P => [tg /setX_P [pa pb pc]]; apply /funI_P; ex_tac.
  by apply: in_graph_Vf.
move/funI_P => [z pa ->]. 
apply:setI2_i; first by rewrite -/(Vf _ _); Wtac.
apply/setX_P; aw;split; fprops; rewrite -/(Vf _ _); Wtac.
Qed.

Lemma restriction_recovers f x:
  function f -> sub x (source f) ->
  restriction f x = triple x (target f) 
    ((graph f) \cap (x \times (target f))).
Proof.
by move=> ff ss; rewrite -(restriction_graph1 ff ss) /restriction; aw.
Qed.

(** Restriction of a function on the source and target *)


Lemma function_rest_of_prolongation f g:
  extends g f -> f = restriction2 g (source f) (target f).
Proof.
move=>[ff fg].
move /(sub_functionP ff fg)=> [_ sts sg] st.
have au: (sub (Vfs g (source f)) (target f)).
  by move =>t /(Vf_image_P fg sts) [u us ->]; rewrite - sg=>//; fprops. 
have ax: (restriction2_axioms g (source f) (target f)) by [].
apply: function_exten;fprops; try solve [rewrite /restriction2; aw;trivial].
  apply: (proj31 (restriction2_prop ax)).
by move => x sf /=; rewrite restriction2_V // sg.  
Qed.


(** ** EII-3-6 Definition of a function by means of a term *) 

(** Function from [a] to [b] associated to the mapping [f] *)

Definition Lf f a b := triple a b (Lg a f).

Lemma lf_source f a b: source (Lf f a b) = a.
Proof. by rewrite /Lf/Lg; aw.  Qed.

Lemma lf_target f a b: target (Lf f a b) = b.
Proof. by rewrite /Lf/Lg; aw.  Qed.

Hint Rewrite lf_source lf_target : aw.

Lemma lf_graph1 f a b c: 
  inc c (graph (Lf f a b)) -> c = J (P c) (f (P c)).
Proof. by rewrite/Lf/Lg; aw;move/funI_P => [z _ ->]; aw. Qed.

Lemma lf_graph2 f a b c:
  inc c a -> inc (J c (f c)) (graph (Lf f a b)).
Proof. by rewrite /Lf/Lg=> ca; aw; apply/funI_P; ex_tac. Qed.

Lemma lf_graph3 f a b c:
  inc c (graph (Lf f a b)) -> inc (P c) a.
Proof. by rewrite /Lf/Lg; aw; move/funI_P=> [z za ->]; aw. Qed.

Lemma lf_graph4 f a b c:
  inc c (graph (Lf f a b)) -> f (P c) = (Q c). 
Proof.  by move=> h; rewrite {2} (lf_graph1 h); aw. Qed.

(** In order for [(Lf f a b)] to be a function, the following must be satisfied *)

Definition lf_axiom f a b :=
  forall c, inc c a -> inc (f c) b. 

Lemma lf_function f a b:
  lf_axiom f a b -> function (Lf f a b).
Proof. 
move=> ta; apply: function_pr; aw; fprops.
by move=> t; rewrite Lg_range; move/funI_P=> [z zb ->]; apply: ta.
Qed.

Lemma lf_function_prop f a b:
  lf_axiom f a b -> function_prop (Lf f a b) a b.
Proof. by move /lf_function =>h; split =>//; aw. Qed.
 
Lemma LfV f a b c: lf_axiom f a b ->  inc c a -> Vf (Lf f a b) c = f c.
Proof. 
by move=> /lf_function ff ca; symmetry; apply:Vf_pr => //; apply: lf_graph2.
Qed. 

Hint Rewrite  LfV : bw.

Lemma lf_recovers f: 
  function f -> Lf (Vf f)(source f)(target f) = f.
Proof. 
move=> ff.
have ta: (lf_axiom (Vf f) (source f) (target f)) by move=> x /=; fprops. 
apply: function_exten; aw=> //; [ by apply: lf_function | by move => x xf; bw].
Qed.

Lemma identity_Lf x: identity x = Lf id x x.
Proof.
have aux: lf_axiom id x x by done.
apply function_exten; fprops; first by apply :lf_function.
by move => t; rewrite lf_source => tx; aw.
Qed.

Lemma restriction_Lf f x: function f -> sub x (source f) ->
 restriction f x = Lf (Vf f) x (target f).
Proof.
move => h1 h2; move: (restriction_prop h1 h2) => [pa pb pc].
have pd: lf_axiom (Vf f) x (target f) by move => t tw; Wtac.
rewrite /restriction; apply: function_exten;aww.
by move => t rs;  rewrite restriction_V //.
Qed.


(** Definition of a constant function and of the constant function *)

Definition constantfp f := function f /\  cstfp f (source f).
Definition constantgp f := fgraph f /\ cstgp f (domain f).

Lemma constant_prop1 f: constantgp f -> small_set (range f).
Proof. 
move=> [ff eq] t1 t2 /(range_gP ff) [x xd ->] /(range_gP ff) [y yd ->]. 
by apply: eq.
Qed.

Lemma constant_prop2 f: constantfp f -> constantgp (graph f).
Proof. move=> [ff eq]; split; fprops; by move:ff=> [_ _ <-].  Qed.

Lemma constant_prop3 x y: constantgp (cst_graph x y).
Proof. 
split; [ fprops | move => a b; rewrite cst_graph_d => ax bx].
by rewrite ! LgV.
Qed.

Lemma constant_prop4 f: function  f -> 
  (constantfp f <-> small_set (Imf f)).
Proof. 
move => ff; split => h.
   rewrite (ImfE ff).
   by apply: constant_prop1; apply: constant_prop2. 
split=> // x x' xs x's; apply: h; Wtac.
Qed.

Definition constant_function A B y := Lf (fun _ : Set => y) A B.

Lemma constant_s A B y: source (constant_function A B y) = A.
Proof. by rewrite /constant_function; aw. Qed.

Lemma constant_t A B y: target (constant_function A B y) = B.
Proof. by rewrite /constant_function; aw. Qed.

Lemma constant_g A B y: graph (constant_function A B y) =  A *s1 y.
Proof. by rewrite /constant_function /Lf corresp_g - cst_graph_pr. Qed.

Lemma constant_f A B y: inc y B -> function (constant_function A B y).
Proof. by move => yB; apply:lf_function. Qed.

Lemma constant_prop A B y: inc y B ->
  function_prop (constant_function A B y) A B.
Proof. by move => yB; apply:lf_function_prop. Qed.

Lemma constant_V A B y x: inc y B -> inc x A ->
 Vf (constant_function A B y) x = y.
Proof. by move => ha hb; rewrite LfV. Qed. 

Lemma constant_constant_fun A B y: inc y B ->
  constantfp (constant_function A B y).
Proof. 
split; first by apply: constant_f.
rewrite constant_s => u v /= us vs; do 2 rewrite constant_V=>//. 
Qed.

Lemma constant_prop6 f:
  constantfp f ->
  f = empty_function_tg (target f) \/ 
  exists2 a, inc a (target f) & f = constant_function (source f) (target f) a.
Proof.
move => [pa pb].
case: (emptyset_dichot (source f)) => h.
  by left; rewrite {1} (empty_source_graph2 pa h).
right; have h':=(rep_i h); have h'' := (Vf_target pa h').
ex_tac; apply: function_exten; rewrite/constant_function;aww.
  by apply: constant_f.  
by  move => i isf; rewrite LfV //; apply: pb.
Qed. 

(** Functions associated to P and Q *)

Definition first_proj g := Lf P g (domain g).
Definition second_proj g := Lf Q g (range g).

Lemma first_proj_V g: {inc g, Vf (first_proj g) =1 P}.
Proof. rewrite /first_proj=> x xg; rewrite LfV // =>t; apply: domain_i1. Qed.

Lemma second_proj_V g: {inc g, Vf (second_proj g) =1 Q}.
Proof. rewrite /second_proj=> x xg; rewrite LfV // =>t; apply: range_i2. Qed.

Lemma first_proj_f g:  function (first_proj g).
Proof. by apply: lf_function =>t; apply: domain_i1. Qed. 

Lemma second_proj_f g: function (second_proj g). 
Proof. by apply: lf_function =>t; apply: range_i2. Qed.


(** ** EII-3-7  Composition of two functions. Inverse function *) 

(** Condition for composition to be a function  *)

Definition composable g f :=  
  [/\ function g, function f &  source g = target f].

Notation "f1 \coP f2" := (composable f1 f2) (at level 50).

Lemma composable_pr f g: g \coP f -> (graph g) \cfP (graph f).
Proof.
move=> [fg ff st]; split; fprops.
by rewrite domain_fg // st; apply: f_range_graph.
Qed.

Lemma compf_graph:
  {when: composable, {morph graph: f g / f \co g >-> f \cf g}}.
Proof. 
move => a b cfg; move:(composable_pr cfg)=> ac.
by rewrite /compose compg_composef; aw.
Qed.

Lemma compf_domg g f:  g \coP f-> 
  domain (graph (g \co f)) = domain (graph f).
Proof. 
by move => cfg; rewrite compf_graph /composef; aw.
Qed.

Lemma compf_s f g: source (g \co f) = source f.
Proof. by rewrite /compose; aw. Qed.

Lemma compf_t f g: target (g \co f) = target g.
Proof. by rewrite /compose; aw. Qed.

Hint Rewrite compf_s compf_t : aw.


(** Proposition 6: composition of functions is a function *)

Theorem compf_f g f: g \coP f -> function (g \co f).
Proof. 
move=> cgf; 
have cd:=(compf_domg cgf).
have ac:=(composable_pr cgf).
have fgcc:= (composef_fgraph (graph g) (graph f)). 
have cg := (compf_graph cgf); rewrite cg in cd.
move: cg; rewrite /compose; aw => ->.
have [fg ff etc] := cgf.
apply: function_pr => //; last by rewrite cd domain_fg. 
apply: (sub_trans (composef_range ac)(f_range_graph fg)).
Qed.

(** Definition of injectivity, surjectivity and bijectivity *)

Definition injection f:=
  function f /\ {inc source f &, injective (Vf f)}.

Definition surjection f :=
  function f /\ 
  (forall y, inc y (target f) -> exists2 x, inc x (source f) & y = Vf f x).

Definition bijection f := injection f /\ surjection f.

(** We give here here some characterizations of injective, surjective, 
bijective functions *)


Lemma inj_function f: injection f -> function f.
Proof. by case. Qed.

Lemma surj_function f: surjection f -> function f.
Proof. by case. Qed.

Lemma bij_function f: bijection f -> function f.
Proof.  by case; case. Qed.

Lemma bij_inj f: bijection f -> {inc source f &, injective (Vf f)}.
Proof. move => h; exact: (proj2 (proj1 h)). Qed.

Lemma bij_surj f: bijection f -> 
   (forall y, inc y (target f) -> exists2 x, inc x (source f) & y = Vf f x).
Proof. move => h; exact: (proj2 (proj2 h)). Qed.

Ltac fct_tac := 
  match goal with
    | H:bijection ?X1 |- function ?X1 => exact (bij_function H)
    | H:injection ?X1 |- function ?X1 => exact (inj_function H)
    | H:surjection ?X1 |- function ?X1 => exact (surj_function H)
    | H:function ?X1 |- correspondence ?X1 =>
      by case H
    | H:function ?g |- sub (range (graph ?g)) (target ?g)
      => apply: (f_range_graph H)
    | H:function ?g |- sub (Imf ?g) (target ?g)
      => apply: (Imf_Starget H)
    | H:composable ?X1 _ |- function ?X1 => exact (proj31 H)
    | H:composable _ ?X1 |- function ?X1 => exact (proj32 H)
    | H:composable ?f ?g |- function (compose ?f ?g ) =>
     apply: (compf_f H)
    | H:function ?f |- function (compose ?f ?g ) =>
     apply: compf_f; split => //
    | H:function ?g |- function (compose ?f ?g ) =>
     apply: compf_f; split => //
    | Ha:function ?f, Hb:function ?g |- ?f = ?g =>
      apply: function_exten
  end.

(** More properties of function composition *)

Lemma compfV g f x: g \coP f ->
  inc x (source f) -> Vf (g \co f) x = Vf g (Vf f x).
Proof.  
rewrite /Vf => cgf xs; rewrite compf_graph=>//. 
apply: composef_ev; rewrite domain_fg  //; fct_tac.
Qed.

Hint Rewrite compfV : bw.

Lemma compfA f g h: f \coP g -> g \coP h -> op_associative compose f g h.
Proof.
move=> cfg chg.
have [gg fh sgth]: g \coP h by []. 
have ffg: (function (f \co g)) by fct_tac.
have fgh: (function (g \co h)) by fct_tac.
have cfgh: (f \co g) \coP h by hnf; aw. 
have cfgh': (f \coP (g \co h)) by move: cfg=> [ff _ etc];hnf; aw.
apply: function_exten; try fct_tac; aw; trivial.
move=> x xh;  bw => //; [ rewrite sgth; Wtac | by aw ].
Qed.

Lemma compf_id_l m:
  function m -> (identity (target m)) \co m = m.
Proof. move=>fm; apply: compf_id_left; fct_tac. Qed.

Lemma compf_id_r m: 
  function m -> m \co (identity (source m)) = m.
Proof. move=> fm; apply: compf_id_right; fct_tac. Qed.

Corollary fcomp_identity_left E:
  {when (fun x => function x /\ (target x) = E),
  left_id (identity E) compose}.
Proof. move => x [cx <-]; exact:compf_id_l. Qed.


Lemma injective_pr f y: injection f ->
   singl_val (fun x => related (graph f) x y).
Proof.
rewrite /related;move=> [ff injf] x x' r1 r2; apply: injf.
- by Wtac.
- by Wtac.
- by rewrite - (Vf_pr ff r1) (Vf_pr  ff r2). 
Qed.

Lemma injective_pr3 f y: injection f ->
   singl_val (fun x => inc (J x y) (graph f)).
Proof. apply: injective_pr.  Qed.

Lemma injective_pr_bis f:
  function f -> (forall y, singl_val (fun x => related (graph f) x y)) ->
  injection f.
Proof. 
move=> ff prop;split => // x y xs ys Weq; apply: (prop (Vf f x) x y).
  by apply: (Vf_pr3 ff  xs).  
by rewrite Weq; apply: (Vf_pr3 ff ys). 
Qed.

Lemma surjective_pr0 f: surjection f -> Imf f = target f.
Proof.
move=> [ff sj]; apply: extensionality; first by apply:(Imf_Starget ff).
move => t tf; move: (sj _ tf) => [x xsf ->].
apply/dirim_P; ex_tac; Wtac.
Qed.

Lemma surjective_pr1 f: function f -> Imf f = target f ->
  surjection f.
Proof.
move=> ff ift; split => // y; rewrite -ift. 
move/dirim_P=> [x pa pb];ex_tac; Wtac.
Qed.

Lemma surjective_pr f y:
  surjection f -> inc y (target f) ->
  exists2 x, inc x (source f) & related (graph f) x y .
Proof. 
move => [ff h] ytf; move: (h _ ytf) => [x xsf ->]; ex_tac.
rewrite /related; Wtac.
Qed.

Lemma surjective_pr5 f:
  function f -> (forall y, inc y (target f) ->
  exists2 x, inc x (source f) & related (graph f) x y) -> surjection f.
Proof. 
move=> ff prop; split => // y yt; move: (prop _ yt) => [x xsf h]; ex_tac.
by apply: Vf_pr.
Qed.

Lemma lf_injective f a b: lf_axiom f a b ->
  (forall u v, inc u a -> inc v a -> f u = f v -> u = v) ->
  injection (Lf f a b).
Proof. 
move=> ta prop; split; first by apply: lf_function. 
by aw; move=> x y xs ys/=; do 2 rewrite LfV=>//; apply: prop. 
Qed.

Lemma lf_surjective f a b: lf_axiom f a b ->
  (forall y, inc y b -> exists2 x, inc x a & y = f x) -> 
  surjection (Lf f a b).
Proof.  
move=> ta prop; split; first by apply: lf_function.
by aw; move=> y yt; case: (prop _ yt)=> x xa fy; ex_tac; rewrite LfV.
Qed.

Lemma lf_bijective f a b: lf_axiom f a b ->
  (forall u v, inc u a -> inc v a -> f u = f v -> u = v) ->
  (forall y, inc y b -> exists2 x, inc x a & y = f x) -> 
  bijection (Lf f a b).
Proof. 
by move => ta pi ps; split; [apply: lf_injective| apply:  lf_surjective].
Qed.

Lemma bijective_pr f y:
  bijection f -> inc y (target f) -> 
  exists! x, (inc x (source f) /\ Vf f x = y).
Proof. 
move=> [[_ inj] [_ sf]] yt; apply /unique_existence; split. 
  by move: (sf _ yt)=> [x p1 p2]; exists x.
by move=> x x' [xs Wx] [x's Wx']; rewrite -Wx' in Wx; apply: inj. 
Qed.

Lemma function_exten4 f g: source f = source g ->
  surjection f -> surjection g ->  {inc source f, f =1f g} ->
  f = g.
Proof.
move=> sfg sf sg Weq.
have ff: function f by fct_tac.
have fg: function g by fct_tac.
have geq: (graph f = graph g).
  by apply: fgraph_exten; fprops; rewrite ! domain_fg.
apply: function_exten1 => //.
by rewrite -(surjective_pr0 sf) -(surjective_pr0 sg) !ImfE// geq.
Qed.


(** Equipotent means there is a bijection between the sets *)

Definition bijection_prop f s t :=
  [/\ bijection f, source f = s & target f = t]. 
Definition surjection_prop f x y:=
  [/\ surjection f, source f = x & target f = y].
Definition injection_prop f x y:= 
  [/\ injection f, source f = x & target f = y].


Lemma identity_fb x: bijection (identity x).
Proof. by apply: lf_bijective => // y yx; exists y. Qed.

Lemma identity_bp x:  bijection_prop (identity x) x x.
Proof. by saw; apply: identity_fb. Qed. 

Lemma imf_ident x: Imf (identity x) = x.
Proof. by rewrite (surjective_pr0 (proj2(identity_fb x))) identity_t. Qed.

(** Injectivity and surjectivity of identity and restriction *) 

Lemma restriction2_fi f x y:
  injection f -> restriction2_axioms f x y ->
  injection (restriction2 f x y).
Proof.
move=> [_ fi] ra.
have [pa pb pc] := (restriction2_prop ra). 
split => //; rewrite pb => a b ax bx.
by do 2 rewrite restriction2_V=>//; apply: fi; apply: (proj42 ra).
Qed.

Lemma restriction2_fs f x y:
  restriction2_axioms f x y ->
  source f = x -> Imf f = y ->
  surjection (restriction2 f x y).
Proof. 
move=> ra sf iy.
have [pa pb pc] := (restriction2_prop ra). 
split => // z; rewrite pb pc - {1} iy - {1} sf.
move /(Imf_P (proj41 ra))=>  [u usf uv].
ex_tac; rewrite restriction2_V //; ue.
Qed.

Lemma restriction1_fs f x:
  function f -> sub x (source f) ->
  surjection (restriction1 f x).
Proof. 
move=> ff sxs.
have [pa pb pc] := (restriction1_prop ff sxs).
split => //y; rewrite pb pc; move/(Vf_image_P ff sxs) => [b bx Jg].
by ex_tac; aw; rewrite restriction1_V.
Qed.

Lemma restriction1_fb f x:
  injection f -> sub x (source f) ->
  bijection (restriction1 f x).
Proof. 
move=> [ff fi] sxf; split; last by apply: restriction1_fs.
have [pa pb pc] :=(restriction1_prop ff sxf).
split => //; rewrite pb => a b ax bx.
by  rewrite ! restriction1_V=>//; apply: fi; apply: sxf.
Qed.

Definition restriction_to_image f := 
  restriction2 f (source f) (Imf f).

Lemma restriction_to_image_axioms f: function f ->
  restriction2_axioms f (source f) (Imf f).
Proof. by move=> ff; split => //; apply :Imf_Starget. Qed.

Lemma restriction_to_imageE f: function f -> 
  restriction_to_image f = restriction1 f (source f).
Proof. by move => ff; rewrite - restriction1_pr. Qed.

Lemma restriction_to_image_fs f: function f ->
  surjection (restriction_to_image f).
Proof. 
by move => h; rewrite (restriction_to_imageE h);apply: restriction1_fs.
Qed.

Lemma restriction_to_image_fb f: injection f ->
  bijection (restriction_to_image f).
Proof. 
by move => h; rewrite (restriction_to_imageE (proj1 h));apply: restriction1_fb.
Qed.

Lemma iim_fun_r f (h:=restriction_to_image f): function f -> 
   forall a, Vfs f a = Vfi (inverse_fun h) a.
Proof.
move => ff a.
have aux:=(proj1 (function_fgraph (proj1 (restriction_to_image_fs ff)))).
rewrite /Vfi/Vfs /inverse_image. 
rewrite corresp_g (igraph_involutive aux) corresp_g. 
congr (direct_image _ a); symmetry;apply/setI2id_Pl. 
exact:(proj2 (proj31 ff)). 
Qed.

(** Extension of a function by adding [f(x)=y] *)

Definition extension f x y:=
  triple ((source f) +s1 x) ((target f) +s1 y)  ((graph f) +s1 (J x y)).

Lemma extension_injective x f g a b:
  domain f = domain g -> ~ (inc x (domain f)) ->
  (f +s1 (J x a) = g +s1 (J x b)) -> f = g.
Proof. 
move=> seq nixsf sv.
set_extens t => tf.
  have: inc t (g +s1 J x b) by rewrite - sv; fprops.
  by case /setU1_P => // ta;case: nixsf; apply /funI_P; ex_tac; rewrite ta;aw.
have: inc t (f +s1 J x a) by rewrite sv; fprops.
case /setU1_P => // ta.
by case: nixsf; rewrite seq;apply /funI_P; ex_tac; rewrite ta;aw.
Qed.

Lemma restr_setU1 f x a:
  fgraph f -> ~ (inc x (domain f)) ->
  restr (f +s1 (J x a)) (domain f) = f.
Proof.
move=> fgf xdf; symmetry.
have aux: fgraph (f +s1 J x a) by apply:fgraph_setU1.
have sd:= (domain_S(@subsetU2l f (singleton (J x a)))).
apply: fgraph_exten; [done | by apply: restr_fgraph | by aw | move=> t tdf].
by rewrite (LgV tdf)  setU1_V_in.
Qed.

Lemma setU1_restr f x E: fgraph f -> ~ (inc x E) ->
   domain f = E +s1 x->
   (restr f E) +s1 (J x (Vg f x)) = f.
Proof.
move=> fgf nxE df.
have sEd: sub E (domain f) by rewrite df; fprops.
have dr: (domain (restr f E)) = E by rewrite restr_d. 
have fgr: fgraph (restr f E) by fprops.
have nxe: ~ inc x (domain (restr f E)) by ue.
apply: fgraph_exten =>//.
    by apply: fgraph_setU1.
  by rewrite domain_setU1 dr df.
move=> u; rewrite domain_setU1 dr; case/setU1_P => uE.
  have ud: inc u (domain (restr f E)) by rewrite dr.
  by rewrite setU1_V_in // restr_ev.
by rewrite uE setU1_V_out.
Qed.

Section Extension.
Variables (f x y: Set).
Hypothesis (ff: function f) (xsf:  ~ (inc x (source f))).

Lemma extension_f: function (extension f x y).
Proof. 
rewrite /extension; apply: function_pr.
- by apply: fgraph_setU1; fprops; rewrite domain_fg.
- rewrite range_setU1 => t /setU1_P [] tr; apply/setU1_P;[left | by right].
  by apply:f_range_graph.
- by rewrite domain_setU1 - (proj33 ff).
Qed.

Lemma extension_Vf_in: {inc (source f), (extension f x y) =1f f}.
Proof.
move=> u uf; symmetry; apply: Vf_pr; first by apply:extension_f.
rewrite /extension; aw; apply: setU1_r;Wtac. 
Qed.

Lemma extension_Vf_out: Vf (extension f x y) x = y.
Proof. 
symmetry;apply: Vf_pr; first by apply:extension_f.
rewrite /extension; aw; apply: setU1_1.
Qed.

Lemma extension_fs: surjection f -> surjection (extension f x y).
Proof. 
move=> [_ sf].
split; first by apply:extension_f.
rewrite /extension; aw => z /setU1_P; case.
  move=> zt; move: (sf _ zt)=> [u us wu].
  by exists u; fprops; rewrite extension_Vf_in.
by move =>->; exists x; fprops; rewrite extension_Vf_out.
Qed.



Lemma extension_restr: 
  restriction2 (extension f x y) (source f) (target f) = f.
Proof.
have pa: restriction2_axioms (extension f x y) (source f) (target f).
  have ha: function (extension f x y) by apply: extension_f.
  have hb: sub (source f) (source (extension f x y)).
    by rewrite /extension; aw; fprops.
  split => //; rewrite /extension; aw; fprops.
  move => t /(Vf_image_P ha hb) [u usf ->]; rewrite (extension_Vf_in usf); Wtac.
move: (restriction2_prop pa) => [pb pc pd].
apply: function_exten => //; rewrite pc => t tx.
by rewrite (restriction2_V pa tx) (extension_Vf_in tx).
Qed.

End Extension.


Lemma extension_fb f x y:  ~ inc x (source f)  -> ~ inc y (target f)  ->
  bijection f ->  bijection (extension f x y).
Proof.
move => ha hb [[ff injf] bf]; split; last by apply:extension_fs.
split; first by apply: extension_f.
rewrite {1}/extension; aw => a b /setU1_P; case => av; move/setU1_P; case => bv.
- rewrite (extension_Vf_in y ff ha av)  (extension_Vf_in y ff ha bv).
  by apply: injf.  
- rewrite bv (extension_Vf_in y ff ha av)  (extension_Vf_out y ff ha).
  move => bad; case:hb; rewrite - bad; Wtac.
- rewrite av (extension_Vf_in y ff ha bv)  (extension_Vf_out y ff ha).
  move => bad; case:hb; rewrite  bad; Wtac.
- by rewrite av bv.
Qed.

Hint Resolve extension_f: fprops.

Lemma extension_f_injective x f g a b:
  function f -> function g -> target f = target g ->
  source f = source g -> ~ (inc x (source f)) ->
  (extension f x a = extension g x b) -> f = g.
Proof.
move=> ff fg teq seq nixsf sv. 
rewrite - (extension_restr a ff nixsf) sv seq teq extension_restr //; ue.
Qed.


(** Canonical injection of a set into a superset *) 
Definition canonical_injection a b :=
  triple a b (identity_g a).

Lemma canonical_injectionE a b: canonical_injection a b = Lf id a b.
Proof. done. Qed.

Lemma ci_fi a b: sub a b -> injection (canonical_injection a b).
Proof. by move => h; rewrite canonical_injectionE; apply:lf_injective. Qed.

Lemma ci_f a b: sub a b -> function  (canonical_injection a b).
Proof. move => h; exact (proj1 (ci_fi h)). Qed.
  
Hint Resolve ci_f : fprops.

Lemma ci_V a b x:
  sub a b -> inc x a -> Vf (canonical_injection a b) x = x.
Proof. 
by move => sab ia; rewrite LfV //.
Qed.

Lemma ci_range a b: sub a b ->
  Imf (canonical_injection a b) = a.
Proof.
by move => ab; rewrite (ImfE (ci_f ab))[graph _]corresp_g identity_r.
Qed.


(** if [h] is constant [h = g \co f], where the target of [f] is a singleton *)
Lemma constant_function_pr2 x h:
  inc x (source h) -> constantfp h ->
  exists g f,
  [/\ g \coP f, h = g \co f, surjection f & singletonp (target f)].
Proof.
move=> xs [fh p]; set (y := Vf h x).
have ssyth: sub (singleton y) (target h) by apply:set1_sub; rewrite /y; fprops.
have ysy: inc y (singleton y) by fprops.
set (g:= canonical_injection (singleton y) (target h)); exists g.
set (f:= constant_function (source h) (singleton y) y); exists f.
have ff: function f by apply: constant_f.
have tf: target f = (singleton y) by rewrite constant_t.
have sf: source f = source h by rewrite constant_s.
have tg: target g = target h by rewrite /g /canonical_injection; aw.
have sg: source g = singleton y by rewrite /g /canonical_injection; aw.
have cop: g \coP f by rewrite /g;split; fprops; rewrite tf. 
split => //.
- apply: function_exten;aw; fprops; try fct_tac.
  move=> z zh; rewrite compfV //; last ue.
  by rewrite (p _ _ zh xs) /f constant_V // ci_V.
- split=>//; rewrite sf tf; move =>z /set1_P ->.
  by exists x; rewrite ?sf ?constant_V.
- by rewrite tf; exists y.
Qed.

(** Diagonal application, maps [x] to [J x x] *) 

Definition diagonal_application a :=
  Lf (fun x=> J x x) a (coarse a).

Lemma diag_app_V a x:
  inc x a -> Vf (diagonal_application a) x = J x x.
Proof. 
by move => xa; rewrite LfV // => y ya;apply: setXp_i.
Qed.

Lemma diag_app_fi a: injection (diagonal_application a).
Proof. 
rewrite /diagonal_application/coarse; apply: lf_injective. 
  by move=> y /=; fprops. 
by move => u v _ _; apply: pr1_def.
Qed.

Lemma diag_app_f a: function (diagonal_application a).
Proof. by case: (diag_app_fi a). Qed.

Lemma diag_app_range a:
  Imf (diagonal_application a) = diagonal a.
Proof. 
rewrite (ImfE (diag_app_f a)) [graph _] corresp_g;set_extens t.
  by move/Lg_range_P => [b ba ->]; apply/diagonal_pi_P.
move/diagonal_i_P => [pt ta pq]; apply/Lg_range_P; ex_tac. 
by rewrite {2} pq pt.
Qed.

(** Injectivity and surjectivity of P and Q *)

Lemma second_proj_fs g: surjection (second_proj g).
Proof.
split; first by apply: second_proj_f.
rewrite /second_proj /range/Lf /Vf; aw.
by move => y /funI_P [z zg ->]; ex_tac; rewrite LgV.
Qed.

Lemma first_proj_fs g: surjection (first_proj g).
Proof. 
split; first by apply: first_proj_f.
rewrite /first_proj /domain/Lf/Vf; aw.
by move => y /funI_P [z zg ->]; ex_tac; rewrite LgV.
Qed.

Lemma first_proj_fi g:
  sgraph g -> (injection (first_proj g) <-> functional_graph g).
Proof. 
move=> gg.
have fpf: (function (first_proj g)) by apply: first_proj_f.
have Ht: source (first_proj g) = g by rewrite/first_proj; aw.
rewrite /injection Ht.
split.
  move=> [_ hyp] a b b'; rewrite /related => i1 i2. 
  suff: (J a b = J a b') by apply: pr2_def.
  by apply: hyp=>//; do 2 rewrite first_proj_V=>//; aw.
move => H;split=>//; move=>x y xg yg/=; do 2 rewrite first_proj_V=>//.
by move/functionalP : (conj gg H) => [_]; apply.
Qed.

(** The function that maps [J x y] to [J y x] *) 

Lemma inv_graph_canon_fb g: sgraph g -> 
    bijection ( Lf (fun x=> J (Q x) (P x)) g (inverse_graph g)).
Proof.  
move => gg; apply: lf_bijective.
+ by move=> c cg /=; apply/igraph_pP; rewrite /related (gg _ cg).
+ move=> u v ug vg peq; apply: pair_exten; try apply: gg=>//.
    by apply: (pr2_def peq).
  by apply: (pr1_def peq).
+ by move=> y /igraphP [py pg]; ex_tac;aw; rewrite  py.
Qed.


(** Proposition 7 summarizes next two theorems. Let f be a function; then 
 f is a bijection if and only if its inverse is a function *)

Theorem bijective_inv_f f:
  bijection f -> function (inverse_fun f).
Proof. 
rewrite /inverse_fun; move => [fi fs].
have gf: (sgraph (graph f)) by move: fi=> [ff _]; fprops.
have fgf: fgraph (inverse_graph (graph f)).
  split; fprops; move=> x y/igraphP [px pf]/igraphP [qx qf] peq.
  apply: pair_exten =>//.
  by rewrite -peq in qf; apply: (injective_pr3 fi pf qf). 
apply: function_pr=>//.
  rewrite igraph_range // domain_fg //; fct_tac.
by rewrite (igraph_domain gf) - (ImfE (proj1 fs)) (surjective_pr0 fs).
Qed.

Theorem inv_function_fb f:
  function f -> function (inverse_fun f) -> bijection f.
Proof. 
move=> ff fif.
split.
  apply: injective_pr_bis=> // x x' y.
  move/igraph_pP;rewrite -ifun_g => r1 ;move/igraph_pP; rewrite -ifun_g=> r2.
  by apply: (fgraph_pr (proj32 fif) r1 r2).
apply: surjective_pr1=> //; rewrite (ImfE ff) - igraph_domain; fprops. 
by rewrite -ifun_g domain_fg //; aw.
Qed.

(** Properties of the inverse of a bijection *)

Lemma ifun_involutive:  {when function, involutive inverse_fun}.
Proof. move=> f ff;apply:icor_involutive; fct_tac. Qed.

Lemma inverse_bij_fb f: bijection f -> bijection (inverse_fun f).
Proof. 
move=> bf;move: (bijective_inv_f bf)=> bif.
have ff:function f by fct_tac.
apply: inv_function_fb => //; rewrite ifun_involutive //.
Qed.

Lemma inverse_V f x:
  bijection f -> inc x (target f) ->
  Vf f (Vf (inverse_fun f) x) = x.
Proof. 
move=> bf xt; move:(bij_surj bf xt) => [y ys xv]; rewrite {2} xv.
move:(bijective_inv_f bf)=> bif.
congr Vf; symmetry; apply:(Vf_pr bif).
rewrite ifun_g xv; apply/igraph_pP; Wtac; fct_tac.
Qed.

Lemma inverse_V2 f y:
  bijection f -> inc y (source f) ->
  Vf (inverse_fun f) (Vf f y) = y.
Proof.
move=> bf ys.
have yt: inc y (target (inverse_fun f)) by aw.
move: (inverse_V (inverse_bij_fb bf) yt).
by rewrite (ifun_involutive (proj1 (proj1 bf))).
Qed.

Lemma inverse_Vis f x:
  bijection f -> inc x (target f) -> inc (Vf (inverse_fun f) x) (source f).
Proof.
move=> bf xt.
have -> : source f=  (target (inverse_fun f)) by aw.
apply: Vf_target; aw;trivial; apply: (proj1(proj1(inverse_bij_fb bf))).
Qed.

Lemma composable_f_inv f: bijection f -> f \coP (inverse_fun f).
Proof.
move=> bf; have fif:=(bijective_inv_f bf).
by split;[fct_tac | done | aw].
Qed.

Lemma composable_inv_f f: bijection f ->  (inverse_fun f) \coP f.
Proof.
move=> bf; have fif:=(bijective_inv_f bf).
split; [ done | fct_tac | by aw].
Qed.

Lemma bij_right_inverse f:
  bijection f ->  f \co (inverse_fun f) = identity (target f).
Proof. 
move=> bf.
have ff: function f by fct_tac.
move:(bijective_inv_f bf)(composable_f_inv bf) => iff cop.
apply: function_exten; aww; first by fct_tac.
by move => a atf;rewrite idV // compfV//; [apply:inverse_V | aw].
Qed.

Lemma bij_left_inverse f:
  bijection f -> (inverse_fun f) \co f = identity (source f).
Proof.
move=> bf.
have ff: function f by fct_tac.
move:(bijective_inv_f bf)(composable_inv_f bf) => iff cop.
apply: function_exten; aww; first by fct_tac; aw.
move => a atf ;rewrite idV // compfV //; aw.
by apply:inverse_V2.
Qed.

Lemma compf_lK f g : bijection g -> g \coP f ->
    (inverse_fun g) \co (g \co f) = f.
Proof.
move => bg cop.
have co1 := (composable_inv_f bg).
rewrite (compfA co1 cop) (bij_left_inverse bg).
by move: cop => [s1 s2 ->]; rewrite (compf_id_l s2).
Qed.

Lemma compf_rK f g : bijection g -> f \coP g ->
     (f \co g) \co (inverse_fun g) = f.
Proof.
move => bg cop.
move: (composable_f_inv bg) => co1.
rewrite -(compfA cop co1) (bij_right_inverse bg).
by move: cop  => [s1 s2 s3]; rewrite - s3 (compf_id_r s1).
Qed.

Lemma compf_regl f f' g : bijection g ->
    f \coP g -> f' \coP g -> f \co g = f' \co g -> f = f'.
Proof.
move => bg pa pb pc.
by rewrite - (compf_rK bg pa) - (compf_rK bg pb) pc.
Qed.

Lemma compf_regr f f' g : bijection g ->
    g \coP f -> g \coP f' -> g \co f = g \co f' -> f = f'.
Proof.
move => bg pa pb pc.
by rewrite - (compf_lK bg pa) - (compf_lK bg pb) pc.
Qed.

Lemma bijection_inverse_aux g h: bijection g -> composable g h ->
  g \co h = identity (source h) -> inverse_fun g = h.
Proof.
move => ha hb.
move: (hb) => [fg fh sgth] w.
have hd:= (composable_inv_f ha).
have ra:=(proj31(bijective_inv_f ha)).
move /(f_equal target): (w); aw; move => tgsh.
have sh: (source h) = source (inverse_fun g) by aw.
move/(f_equal (compose (inverse_fun g))): w.
rewrite sh (compf_id_right ra) (compfA hd hb) (bij_left_inverse ha).
by rewrite sgth (compf_id_left (proj31 fh)).
Qed.



(** Properties of direct and inverse images *)

Lemma sub_inv_im_source f y:
  function f -> sub y (target f) -> 
  sub (Vfi f y) (source f).
Proof. by move=> ff yt t /iim_graph_P [u uy Jg]; Wtac. Qed.

Lemma direct_inv_im f y:
  function f ->  sub y (target f) -> 
  sub (Vfs f (Vfs (inverse_fun f) y)) y.
Proof.
move=> ff yt x. 
have aux: sub (Vfs (inverse_fun f) y) (source f). 
  by rewrite /inverse_fun/Vfs; aw; apply: sub_inv_im_source.
move/(Vf_image_P ff aux) =>[u /dirim_P  [z zy /igraph_pP]].
by rewrite - ifun_g (ifun_involutive ff) => xx ->; rewrite -(Vf_pr ff xx).
Qed.

Lemma nonempty_image f x:
  function f -> nonempty x -> sub x (source f) ->
  nonempty (Vfs f x).
Proof.
move=> ff [z zx] xf; exists (Vf f z); apply/dirim_P; ex_tac; Wtac. 
Qed.

Lemma direct_inv_im_surjective f y:
  surjection f -> sub y (target f) -> 
  Vfs f (Vfs (inverse_fun f) y) = y. 
Proof.
move=> [ff sf] yt.
apply: extensionality; first by apply: direct_inv_im. 
move=> x xs; rewrite -iim_fun_pr.
apply/Vf_image_P =>//; first by apply: sub_inv_im_source. 
have [u us Jg] := (sf _ (yt _ xs)).
exists u=>//;apply/iim_fun_P; ex_tac;rewrite Jg; Wtac.
Qed.

Lemma inverse_direct_image  f x:
  function f -> sub x (source f) ->
  sub x (Vfs (inverse_fun f) (Vfs f x)).
Proof.
move=> ff sxf t tx.
apply/dirim_P; exists (Vf f t). 
  by apply/Vf_image_P => //; ex_tac.
rewrite ifun_g; apply/igraph_pP; Wtac.
Qed.

Lemma inverse_direct_image_inj f x:
  injection f -> sub x (source f) ->
  Vfs (inverse_fun f) (Vfs f x) = x.
Proof.
move=> [ff fi] xsf. 
apply: extensionality; last by apply: inverse_direct_image.
rewrite -iim_fun_pr => y /iim_graph_P [u ui Jg].
move /(Vf_image_P ff xsf): ui => [v vx]; rewrite (Vf_pr ff Jg) => Vv.
by rewrite - (fi _ _  (xsf _ vx) (p1graph_source ff Jg) (sym_eq Vv)).
Qed.


(** ** EII-3-8 Retractions and sections *)

(** Definition of left and right inverse *)

Definition is_left_inverse f r:=
  r \coP f /\ r \co f = identity (source f).

Definition is_right_inverse f s:=
  f \coP s /\ f \co s = identity (target f).


Lemma left_i_target f r: is_left_inverse f r ->  target r = source f.
Proof. by move=> [_ /(congr1 target)]; aw. Qed.

Lemma left_i_source f r: is_left_inverse f r ->  source r = target f.
Proof. by move=> [[_ [_ c] _]]. Qed.

Lemma right_i_source f s:  is_right_inverse f s ->  source s = target f.
Proof. by move=> [_ /(congr1 source)]; aw. Qed.

Lemma right_i_target f s: is_right_inverse f s ->  target s = source f.
Proof. by move=> [[_ [_ c] _]]. Qed.

Lemma right_i_V f s x:
  is_right_inverse f s -> inc x (target f) -> Vf f (Vf s x) = x.
Proof. 
move=> rsf xtf; move: (xtf);rewrite - (right_i_source rsf).
by move: rsf=> [csf c] xs;rewrite - compfV // c; bw.
Qed.

Lemma left_i_V f r x:
  is_left_inverse f r -> inc x (source f) -> Vf r (Vf f x) = x.
Proof. by move=> [ltf c] xsf; rewrite- compfV // c ; bw.  Qed.


(** Proposition 8 concerns the next 4 theorems; it is the link between
 injectivity, surjectivity and existence of left and right inverse *)

Theorem inj_if_exists_left_inv f:
  (exists r, is_left_inverse f r) -> injection f.
Proof.
move=> [r lrf]; split; first by move: lrf => [ cp _ ]; fct_tac.
move=> x y xs ys sv.
by rewrite  - (left_i_V lrf xs) - (left_i_V lrf ys) sv. 
Qed.

Theorem surj_if_exists_right_inv f:
  (exists s, is_right_inverse f s) -> surjection f.
Proof. 
move=> [s rsf]; move: (rsf) => [cp _]; move: (cp) =>[ff fs ss].
split => // y yt; exists (Vf s y).
  rewrite -(right_i_source rsf) in yt; rewrite ss; fprops.
by rewrite (right_i_V rsf yt). 
Qed.

(** Existence of left and right inverse for Bourbaki functions *)

Theorem exists_left_inv_from_inj f:
  injection f -> nonempty (source f) -> exists r, is_left_inverse f r.
Proof. 
move=> fi [a asf]; move: (inj_function fi) => ff.
pose p x y := x = Vf f y.
pose gx x := (select (p x) (source f)).
have hc x:  inc x (Imf f) -> p x (gx x) /\ inc (gx x) (source f). 
  move => xI; apply: select_pr; first by move/(Imf_P ff): xI.
  rewrite /p; move => i j /=  isf e1 jsf e2;apply: (proj2 fi i j isf jsf).
  by rewrite - e1 e2.
pose g x := Yo (inc x (Imf f)) (gx x) a.
have ax: lf_axiom g (target f) (source f).
  rewrite /g => t tt; Ytac h => //; exact:(proj2 (hc _ h)).  
have ha: Lf g (target f) (source f) \coP f.
  by saw; apply:lf_function. 
exists (Lf g (target f) (source f)).
split => //; apply: function_exten; aw; fprops; first by fct_tac.
move => y ys /=.
have yi:inc (Vf f y) (Imf f) by  apply/(Imf_P ff); ex_tac.
have ft: inc (Vf f y) (target f) by Wtac.
move: (hc _ yi) => [hu hv]; move:(proj2 fi _ _ ys hv hu) => yv.
by rewrite LfV // compfV // LfV // /g; Ytac0.
Qed.

Theorem exists_right_inv_from_surj f:
  surjection  f -> exists s, is_right_inverse f s.
Proof. 
move=> [ff sf].
pose p y x := inc x (source f) /\ Vf f x = y.
have ha y: inc y (target f) -> p y (choose (p y)).
  by move => /sf [x xa xb]; apply: choose_pr; exists x.
have ax: lf_axiom (fun y => choose (p y)) (target f) (source f).
  by move => y /ha; case.
have hb: f \coP Lf (fun y : Set => choose (p y)) (target f) (source f).
   by saw; apply: lf_function.
exists (Lf (fun y => choose (p y)) (target f) (source f)).
split => //;apply:function_exten; aw; fprops; first by fct_tac.
move => y yt; rewrite idV // compfV //; last by aw.
rewrite LfV//; exact:proj2 (ha _ yt).
Qed.

(** If compositions in both order are the identity, then the functions are bijections *)

Lemma bijective_from_compose g f:
  g \coP f -> f \coP g -> g \co f = identity (source f) ->
  f \co g = identity (source g)  ->
  [/\ bijection f, bijection g & g = inverse_fun f].
Proof. 
move=> cgf cfg cgfi cfgi.
move: (cfg) (cgf)=> [ff fg seq] [_ _ teq].
have injf: injection f by apply: inj_if_exists_left_inv; exists g. 
have injg: injection g by apply: inj_if_exists_left_inv; exists f. 
have bf: (bijection f).
  by split =>//; apply: surj_if_exists_right_inv; exists g; hnf; rewrite -teq.
split=>//.
  by split=>//; apply: surj_if_exists_right_inv; exists f; hnf; rewrite - seq.
have fif:= (bijective_inv_f bf).
apply: function_exten; aw => // => x xs.
have {2} -> : (x = Vf f (Vf g x)).
  by rewrite - compfV=>//;rewrite cfgi idV =>//.
rewrite (inverse_V2 bf) // seq; Wtac.
Qed.

(** More links between left inverse and right inverse *)

Lemma right_inverse_from_left f r:
  is_left_inverse f r -> is_right_inverse r f.
Proof. by move=> [c e];hnf; rewrite (left_i_target (conj c e)). Qed.

Lemma left_inverse_from_right f s:
  is_right_inverse f s -> is_left_inverse s f.
Proof. by move=> [c e]; hnf; rewrite (right_i_source (conj c e)). Qed.

Lemma left_inverse_fs f r:
  is_left_inverse f r -> surjection r.
Proof.
move=> lrf; apply: surj_if_exists_right_inv. 
by exists f; apply: right_inverse_from_left.
Qed.

Lemma right_inverse_fi f s:
  is_right_inverse f s -> injection s.
Proof. 
move=> lrf; apply: inj_if_exists_left_inv. 
by exists f; apply: left_inverse_from_right.
Qed.

Lemma section_unique f:
  {when (is_right_inverse f) &, injective Imf }.
Proof. 
move=> s s' rsf rs'f rg.
move: (proj32_1 rsf)(proj32_1 rs'f) => fs fs'.
move: (right_i_source rsf) (right_i_source rs'f) => ss ss'.
apply: function_exten =>//.
    by rewrite  (right_i_source rsf).
  by rewrite  (right_i_target rsf)  (right_i_target rs'f).
move=> x xs.
move: (Imf_i fs xs).
move: xs;rewrite rg ss => xs /(Imf_P fs') [y]; rewrite ss' => ys ww.
move: (f_equal (fun z => Vf f z) ww).
by rewrite(right_i_V rs'f ys)  (right_i_V rsf xs) ww => ->.
Qed.

(** Theorem one is next 14 lemmas. It studies left and right invertibility 
of one of f g and the composition of f and g, given properties of the 
other objects. *)


Theorem compose_fi f f':
  injection f -> injection f' -> f' \coP f -> injection (f' \co f).
Proof. 
move=> [_ fi] [_ fi'] c; split; first by  fct_tac.
aw => x y xs ys; rewrite !compfV // =>p; apply: (fi _ _ xs ys).
move:c => [_ ff c]; apply: fi'  => //;   rewrite c; Wtac.
Qed.

Lemma inj_compose1 f f':
  injection f -> injection f' -> source f' = target f ->
  injection (f' \co f).
Proof. 
move=> injf injf' sff';apply: compose_fi=> //;split => //; fct_tac. 
Qed.

Theorem compose_fs f f':
  surjection f -> surjection f' -> f' \coP f -> surjection (f' \co f).
Proof. 
move=> [_ sf] [_ sf'] c; split; [fct_tac | aw => y yt].
move: (sf' _ yt) => [x xs ->].
have xt: inc x (target f) by rewrite - (proj33 c).
by move: (sf _ xt) => [z zs ->]; ex_tac;rewrite compfV.
Qed.

Lemma compose_fb f f':
  bijection f -> bijection f' -> f' \coP f -> bijection (f' \co f).
Proof. 
by move=> [inf sf] [inf' sf']; split ; [apply: compose_fi | apply: compose_fs].
Qed.

Lemma right_compose_fb f f':
  f' \coP f -> bijection (f' \co f) -> bijection f' -> bijection f.
Proof. 
move=> c bc bf; move: (inverse_bij_fb bf) => bf'.
rewrite - (compf_lK bf c);apply: compose_fb => //; saw;fct_tac.
Qed.

Lemma left_compose_fb f f':
  f' \coP f -> bijection (f' \co f) -> bijection f -> bijection f'.
Proof. 
move=> cff bc bf; move: (inverse_bij_fb bf) => bf'.
rewrite -(compf_rK bf cff); apply: compose_fb => //; saw; fct_tac.
Qed.

Lemma left_inverse_composable f f' r r': f' \coP f ->
  is_left_inverse f' r' -> is_left_inverse f r -> r \coP r'.
Proof.
move=> [_ _ c] li1 [[fr _ r1] _].
move: (left_i_target li1)=> r2.
move: li1=> [[fr' _] _ _].
by split => //; rewrite r1 - c r2.
Qed.

Lemma right_inverse_composable f f' s s': f' \coP f ->
  is_right_inverse f' s' -> is_right_inverse f s -> s \coP s'.
Proof. 
move=> [_ _ c]  [[_ fs r1] _] ri1.
move: (ri1)=> [[_ fs' _] _].
by  split => //; rewrite (right_i_source ri1) -c. 
Qed.

Theorem left_inverse_compose f f' r r': f' \coP  f ->
  is_left_inverse f' r' -> is_left_inverse f r ->
  is_left_inverse (f' \co f) (r \co r') .
Proof.
move=> c1 li1 li2.
have cc:= left_inverse_composable c1 li1 li2.
have tr'sr':= left_i_target li1.
have sf'sr: (source f' = source r) by rewrite (proj33 cc).
have sr'tf':= left_i_source li1.
have [crf' crfi'] := li1.
have [crf crfi] := li2.
split.
  by split; [ fct_tac | fct_tac | aw;rewrite sr'tf'].
have crrf: (r \co r') \coP f' by split; [ fct_tac | fct_tac| aw ].
rewrite compfA //- (@compfA r r' f') //. 
rewrite crfi' sf'sr compf_id_r ?crfi; aw; trivial;fct_tac.
Qed.

Theorem right_inverse_compose f f' s s': f' \coP f ->
  is_right_inverse f' s' -> is_right_inverse f s ->
  is_right_inverse (f' \co f) (s \co s').
Proof.
move=> cf'f ri1 ri2.
have css':= (right_inverse_composable cf'f ri1 ri2).
have sstf:= (right_i_source ri2).
have tssf:=(right_i_target ri2).
have sf'sr: (target f = target s') by rewrite - (proj33 css').
have [cfs' cfsi'] := ri1.
have [cfs cfsi] := ri2.
split.
  by split; [ fct_tac |  fct_tac | aw;rewrite -tssf].
have crrf: f \coP (s \co s') by split; [ fct_tac | fct_tac| aw ].
rewrite - compfA=>//; rewrite (@compfA f s s')=>//. 
by aw; rewrite cfsi sf'sr compf_id_l=>//; fct_tac.
Qed.

Theorem right_compose_fi f f':
  f' \coP f -> injection (f' \co f) -> injection f.
Proof. 
move=> cff [fc ic];split; first by fct_tac.
by move: ic; aw=> ic x y xs ys eql; apply: ic => //; rewrite !compfV //; ue.
Qed.

Theorem left_compose_fs f f':
  f' \coP f -> surjection (f' \co f) -> surjection f'.
Proof. 
move=> cff sc; split; first by fct_tac.
have: (target f' = target (f' \co f)) by aw.
move=> -> y yt; move: ((proj2 sc) _  yt)=> [x xs ->].
rewrite compf_s in xs; exists (Vf f x); last by apply compfV.
move:cff=> [_ ff ->]; fprops. 
Qed.

Theorem left_compose_fs2 f f':
  f' \coP f-> surjection (f' \co f) -> injection f' -> surjection f.
Proof. 
move=> cff sc [_ fi].
have  [ff ff' eq] := cff.
split; first by fct_tac.
rewrite - eq=>y ytf.
have ytc: (inc (Vf f' y) (target (f' \co f))) by aw; fprops.
move: ((proj2 sc) _  ytc)=> [x]; aw => xs; rewrite compfV // => eq1.
by exists x => //; apply: fi=>//;  rewrite eq; fprops.
Qed.

Theorem left_compose_fi2 f f':
  f' \coP f -> injection (f' \co f) -> surjection f -> injection f'.
Proof. 
move=>  cff [_ ic] sf.
split; first by fct_tac.
rewrite (proj33 cff) => x y xs ys.
have [x' x's e1] := ((proj2 sf) _  xs).
have [y' y's e2] :=((proj2 sf) _  ys).
rewrite compf_s in ic; move: (ic _ _ x's y's).
by rewrite !compfV // e1 e2 => e3 e4; rewrite (e3 e4).
Qed.

Theorem left_inv_compose_rf f f' r'':
  f' \coP f -> is_left_inverse (f' \co f) r'' -> 
  is_left_inverse f (r'' \co f').
Proof.
move=> cff [[ aa bb]]; aw; move => crffi cc.
have [ff' ff seq]: f' \coP f by [].
have crf: r'' \coP  f' by hnf.
split; [saw; fct_tac | by rewrite - compfA ].
Qed.

Theorem right_inv_compose_rf f f' s'':
  f' \coP f -> is_right_inverse  (f' \co f) s'' -> 
  is_right_inverse f' (f \co s'').
Proof. 
move=> cff [[ fc fs]]; aw => cffsi cc. 
have [ff' ff seq]: (f' \coP f) by [].
have cfs: f \coP s'' by  hnf. 
by split; [saw; fct_tac | rewrite compfA ].
Qed.

Theorem left_inv_compose_rf2 f f' r'':
  f' \coP f -> is_left_inverse (f' \co f) r'' -> surjection f ->
  is_left_inverse f' (f \co r'').
Proof. 
move=> cff lic sf.
have bf: (bijection f). 
  split=>//.
  have: (injection (f' \co f)) by apply: inj_if_exists_left_inv; exists r''. 
  by apply: (right_compose_fi cff).
move: (left_i_target lic); aw=> trsf; move:lic=> [crrf]; aw=> crrfi.
have cfr: f \coP r'' by  hnf;split; try fct_tac; symmetry.
have fcfr:(function  (f \co r'')) by fct_tac.
split; first by hnf; split;  try fct_tac; move: crrf=> [_  _]; aw.
set (invf:= inverse_fun f).
have sfti: (source f = target invf) by rewrite /invf; aw. 
have fi:(function invf) by  apply: bijective_inv_f.
have cffi: (f' \co f) \coP invf by hnf; aw; split; try fct_tac. 
have co3: r'' \coP ((f' \co f) \co inverse_fun f).
  by  hnf; split;try fct_tac;move: crrf=> [_ _]; aw.
have co4: r'' \coP f' by hnf; split; try fct_tac;move: crrf=> [_ _]; aw.
rewrite - (compfA cfr co4) -{1} (compf_rK bf cff) (compfA crrf cffi). 
by rewrite crrfi sfti compf_id_l // /invf (proj33 cff) bij_right_inverse. 
Qed.

Theorem right_inv_compose_rf2 f f' s'':
  f' \coP f -> is_right_inverse (f' \co f) s'' -> injection f' ->
  is_right_inverse f (s'' \co f').
Proof. 
move=> cff risc fi.
have sc: (surjection (f' \co f)) by apply:surj_if_exists_right_inv; exists s''.
have bf': (bijection f') by split=>//; apply: (left_compose_fs cff sc).  
move: (right_i_source risc); aw=> sstf.
move: risc=> []; aw => cffs cffsi.
have csf: (s'' \coP f') by hnf; split;  try fct_tac. 
have fcsf: function (s'' \co f') by fct_tac.
have cfc: f \coP (s'' \co f') by hnf; split; try fct_tac; move:cffs=> [_ _]; aw.
have bif:= (bijective_inv_f bf').
have sf'tf: source f' = target f by move: cff=> [_ _].
set (invf:= inverse_fun f').
have cic: composable invf (f' \co f) by split; try fct_tac; rewrite/invf; aw.
have cffsf: (f' \co f) \coP (s'' \co f').
  hnf; split;[ fct_tac |  done | by move:cfc=> [_ _]; aw ].
have ff: function f' by fct_tac.
split=>//.
rewrite - {1} (compf_lK bf' cff) - compfA // (compfA cffs csf).
by rewrite  cffsi compf_id_l // (bij_left_inverse bf') sf'tf.
Qed.


(** Proposition 9  is the next 6 lemmas (each in 2 variants). Given f and g, 
when does there exists h such that the composition with f (in any order) is g *)

Theorem exists_left_composable f g:
  function f -> surjection g -> source f = source g ->
  ((exists h, h \coP g /\ h \co g = f) 
   <->  (forall x y, inc x (source g) -> inc y (source g) -> 
       Vf g x = Vf g y -> Vf f x = Vf f y)).
Proof. 
move=> ff sg sfsg; split.
  by move=> [h [chg]] <- x y xs ys; rewrite !compfV // => ->.
move:(exists_right_inv_from_surj sg) => [h [ha hb]] hc.
move: ha => [fg fh sgth].
have ra: f \coP h by split => //; rewrite sfsg. 
have rb: function (f \co h) by apply:compf_f.
have rc: source h = target g by move: (f_equal source hb); aw.
have rd: (f \co h) \coP g by split; aw.
have re: g \coP h by split.
exists (f \co h); split => //.
symmetry; apply: function_exten; aw;trivial; first by apply:compf_f.
move => x xsf /=.
have xsg: inc x (source g) by ue.
have gxsh: inc (Vf g x) (source h) by rewrite rc; Wtac.
have hgxsg: inc (Vf h (Vf g x)) (source g) by rewrite  sgth; Wtac.
rewrite!compfV //; apply: (hc _ _ xsg hgxsg).
move: (f_equal (Vf ^~ (Vf g x)) hb). rewrite compfV // idV //; Wtac.
Qed.

Theorem exists_left_composable_aux f g s h:
  function f -> source f = source g ->
  is_right_inverse g s ->
  h \coP g -> h \co g = f -> h = f \co s.
Proof. 
move=> gg sfsg [csg cshi] chg <-. 
have shtg:(source h= target g) by move: chg=> [_ _].
by rewrite - compfA // cshi - shtg compf_id_r //; fct_tac. 
Qed.

Theorem exists_unique_left_composable f g h h':
  function f -> surjection g -> source f = source g ->
  h \coP g -> h' \coP g -> 
  h \co g = f ->  h' \co g = f -> h = h'.
Proof.
move=> ff sg sfsg chg chg' chgf  chgf'.
move:(exists_right_inv_from_surj sg)=> [j jp].
rewrite (exists_left_composable_aux ff sfsg jp chg chgf).
by rewrite (exists_left_composable_aux ff sfsg jp chg' chgf').
Qed.


Theorem left_composable_value f g s h:
  function f -> surjection g -> source f = source g ->
  (forall x y, inc x (source g) -> inc y (source g) -> 
    Vf g x = Vf g y -> Vf f x = Vf f y) ->
  is_right_inverse g s  ->  h =  f \co s -> h \co g = f.
Proof. 
move=> ff sg sfsg hyp rish ->.
have sstg:= (right_i_source rish).
have [cgs cgsi] := rish.
have cfs: f \coP s by hnf; split; [done |fct_tac | move:cgs => [_ _] <-].
have cfsg: (f \co s) \coP g by hnf; saw;fct_tac.
apply: function_exten; aw => //; first by fct_tac.
move=> x xg.
have Ws: (inc (Vf g x) (source s)) by rewrite sstg;Wtac;fct_tac.
have WWs: inc (Vf s (Vf g x)) (source g).
    move:cgs => [_ _ ->]; Wtac; fct_tac.
rewrite !compfV //; apply:  hyp =>//; rewrite -compfV // cgsi idV //.
by rewrite - sstg. 
Qed.

Theorem exists_right_composable_aux f g h r:
  function f ->  target f = target g ->
  is_left_inverse g r  -> g \coP h -> g \co h = f ->
  h = r \co f.
Proof.
move=> ff tftg [crg crgi] chg <-; rewrite compfA // crgi.
by move:chg=> [_ fh ->];rewrite compf_id_l. 
Qed.


Theorem exists_right_composable_unique f g h h':
  function f -> injection g -> target f = target g ->
  g \coP h ->  g \coP h' -> 
  g \co h = f -> g \co h' = f -> h = h'.
Proof.
move=> ff [_ ig] tftg cgh cgh' cghf cghf'.
move: (cgh)(cgh') => [p1 p2 p3] [_ p5 p6].
rewrite -cghf' in cghf.
have shh': source h = source h' by rewrite -(compf_s h g) -(compf_s h' g) cghf.
apply: function_exten => //; [ ue | move=> x xsh;apply: ig ].
+ by rewrite p3; Wtac.
+ rewrite p6; Wtac; ue.
+ move: (f_equal (Vf ^~  x) cghf); rewrite !compfV //; ue.
Qed.

Theorem exists_right_composable f g:
  function f -> injection g -> target f = target g ->
  ((exists h, g \coP h /\ g \co h = f) <->  (sub (Imf f) (Imf g))).
Proof. 
move=> ff ig tftg.
have fg: function g by fct_tac.
split.
  move => [h [chg cghf]] x /(Imf_P ff) [u usf ->]; apply/(Imf_P fg).
  have [_ fh th] := chg.
  move: usf; rewrite - cghf compf_s => usg;
  exists (Vf h u);  [rewrite th; Wtac | rewrite compfV //].
case: (emptyset_dichot (source g)).
  case: (emptyset_dichot (source f)).
    move=> ssfe sge _.
    move: empty_function_function => [qa qb qc].
    have cge: (g \coP empty_function) by split => //; rewrite qc.
    exists (empty_function); split=>//; symmetry.
    apply: function_exten;aw =>//;try fct_tac; rewrite ssfe ?qb //.
    move => x /in_set0 //.
  move=> [x xsf] sge hyp.
  move: (hyp _ (Imf_i ff xsf)); move/(Imf_P fg) => [u].
  by rewrite sge => /in_set0. 
move=> nesg hyp.
have [r rli]:= (exists_left_inv_from_inj ig nesg).
have trsg:= (left_i_target rli).
have [crg crgi] := rli.
have crf: (r \coP f).
   by hnf; split => // ; first (by fct_tac); move: crg=> [_ _ ->]; symmetry.
have fcrf: (function (r \co f)) by fct_tac.
have cgrf: (g \coP (r \co f)) by hnf; aw. 
exists (r \co f); split=>//.
symmetry;apply: function_exten;aw =>  //; first by  fct_tac; aw.
move=> x xsf. rewrite !compfV //; last by aw.
have: (inc (Vf f x) (Imf g)) by apply: hyp; Wtac.
move/(Imf_P fg)  => [z zs ->].
have: (Vf (r \co g) z = z) by rewrite crgi idV.
by rewrite  compfV // => ->.
Qed.


Theorem right_composable_value f g r h:
  function f -> injection g -> target g = target f ->
  is_left_inverse g r ->
  (sub (Imf f) (Imf g)) ->
  h = r \co f -> g \co h = f.
Proof. 
move=> ff ig tgtf lirg hyp ->.
have trsg :=(left_i_target lirg).
have [crg crgi] := lirg.
have srtg:=(proj33 crg).
have crf: (r \coP f)  by split=> //; try fct_tac; rewrite srtg.  
have cgrf: g \coP (r \co f)  by split; try fct_tac; symmetry; aw. 
have cgr: (g \coP r) by split => //; fct_tac. 
apply: function_exten; aw; trivial;try fct_tac.
move=> x xf; rewrite !compfV //; last by aw.
have: (inc (Vf f x) (Imf g)) by apply: hyp;Wtac.
move/(Imf_P (proj1 ig))=> [y ys ->].
by move: (f_equal (fun z=> (Vf z y)) crgi); rewrite compfV // idV // => ->.
Qed.

(** Equipotent *)

Definition equipotent x y := 
  exists z, bijection_prop z x y.

Notation "x \Eq y" := (equipotent x y) (at level 50).

Lemma equipotent_aux f a b:
  bijection (Lf f a b) -> a \Eq b.
Proof. by move => h; exists (Lf f a b); rewrite /bijection_prop; aw; split. Qed.

Lemma equipotent_bp f a b:
  bijection_prop f a b -> a \Eq b.
Proof. by exists f.  Qed.


Lemma EqR: reflexive_r equipotent.
Proof. move => x; exists (identity x); apply: identity_bp. Qed.

Hint Resolve EqR: fprops.

Lemma EqT: transitive_r equipotent.
Proof. 
move => c b a [f [bf sf tf]] [g [bg sg tg]]; exists (g \co f).
split; aw => //.
by apply: compose_fb => //; split => //; try fct_tac; rewrite tf.
Qed.

Lemma EqS: symmetric_r equipotent.
Proof.
move => a b [f [bf sf tf]]; exists (inverse_fun f).
by  saw; apply:inverse_bij_fb. 
Qed.


Lemma Eq_restriction1 f x:
  sub x (source f) -> injection f ->
  x \Eq (Vfs f x).
Proof. 
move=> wsf bf; have h:=(restriction1_fb bf wsf). 
by exists (restriction1 f x); split => //; rewrite/restriction1; aw.
Qed.

Lemma Eq_src_range f: injection f -> 
  (source f) \Eq (Imf f).
Proof. 
move=> injf; apply: Eq_restriction1; fprops.
Qed.


Lemma Eq_setX2_S a b:
  (a \times b) \Eq (b \times a).
Proof.
have pa: sgraph (a \times b) by fprops.
by move: (inv_graph_canon_fb pa); rewrite igraphX  => / equipotent_aux.
Qed.

Lemma Eq_indexed a b:  a \Eq (a *s1 b).
Proof.
rewrite /indexed.
apply: (@equipotent_aux (fun x=> J x b)); apply: lf_bijective.
- by move=> x xa /=; aw; fprops. 
- by move=> u v _ _; apply: pr1_def.
- move=> y /setX_P [py pya /set1_P <-]; ex_tac; aw.
Qed.

Lemma Eq_indexed2 a b: (a *s1 b) \Eq a.
Proof. apply:EqS; apply: Eq_indexed. Qed.

Lemma Eq_indexed3 a b c: (a *s1 b) \Eq (a *s1 c).
Proof. apply: (EqT (Eq_indexed2 a b) (Eq_indexed a c)). Qed.

Lemma Eq_rindexed a b: a \Eq (indexedr b a).
Proof.
by apply: (EqT (Eq_indexed a b)); apply: Eq_setX2_S.
Qed.


Lemma Eq_mulA a b c:
  (a \times (b \times c)) \Eq ((a \times b) \times c).
Proof.
pose g z := J (J (P z) (P (Q z))) (Q (Q z)).
exists (Lf g  (a \times (b \times c)) ((a \times b) \times c)); split; aww.
apply: lf_bijective.
+ move=> d /setX_P [pa pb] /setX_P [pc pd pe].
  apply:setXp_i => //;  apply:setXp_i => //.
+ move=> u v /setX_P  [pu Pu]  /setX_P [pQu PQu QQu] 
             /setX_P [pv Pv]  /setX_P [pQv PQv QQv] eq.
  move:(pr1_def eq)(pr2_def eq)=> eq1 eq2. 
  move:(pr1_def eq1)(pr2_def eq1)=> eq3 eq4. 
  apply: pair_exten=>//; apply: pair_exten =>//. 
move => y  /setX_P  [py]  /setX_P [pPy PP QP] Qc.
exists (J (P (P y)) (J (Q (P y)) (Q y))) => //.
  apply:setXp_i => //;  apply:setXp_i => //.
by rewrite /g !(pr1_pair,pr2_pair) pPy py. 
Qed.

Lemma Eq_src_graph f: function f -> (source f) \Eq (graph f).  
Proof.
move=> ff.
apply: (@equipotent_aux (fun z => J z (Vf f z)));apply: lf_bijective.
- move=> z jz /=;Wtac.
- move=> u v _ _ aux; exact: (pr1_def aux).
- move=> y yG; move: (p1graph_source1 ff yG) => pa; ex_tac.
  apply: in_graph_V => //; fprops.
Qed.

Lemma Eq_domain f: fgraph f -> domain f \Eq f.
Proof.
move => h.
apply:(@equipotent_aux (fun z => J z (Vg f z))); apply: lf_bijective.
+ by apply: fdomain_pr1.
+ by move => u v _ _ /pr1_def.
+ by move => y yf; rewrite (in_graph_V h yf); exists (P y); fprops.
Qed. 



(** ** EII-3-9 Functions of two arguments *)

(** Given a function f with two arguments and one argument, 
we obtain a function of one argument*)

Definition partial_fun2 f y :=
  Lf (fun x=> Vf f (J x y)) (im_of_singleton (inverse_graph (source f)) y) 
    (target f).

Definition partial_fun1 f x :=
  Lf(fun y=> Vf f (J x y))(im_of_singleton (source f) x) (target f).

Section Funtion_two_args.
Variable f:Set.
Hypothesis ff: function f.
Hypothesis sgf: sgraph (source f).

Lemma partial_fun1_axioms x: 
  lf_axiom (fun y=> Vf f (J x y))(im_of_singleton (source f) x) (target f).
Proof. move=> t /dirim_P [u /set1_P ->]; fprops. Qed.

Lemma partial_fun1_f x: function (partial_fun1 f x).
Proof. by apply: lf_function; apply: partial_fun1_axioms.  Qed.

Lemma partial_fun1_V x y: 
  inc (J x y) (source f) -> Vf (partial_fun1 f x) y = Vf f (J x y) .
Proof.
move => Js; rewrite LfV //; first  by apply: partial_fun1_axioms.
apply /dirim_P; ex_tac; fprops.
Qed.

Lemma partial_fun2_axioms  y: 
  lf_axiom (fun x=>Vf f (J x y))(im_of_singleton (inverse_graph (source f)) y)
  (target f).
Proof. move=> t /iim_graph_P [u /set1_P ->]; fprops. Qed.

Lemma partial_fun2_f y: function (partial_fun2 f y).
Proof. by apply: lf_function; apply: partial_fun2_axioms.  Qed.

Lemma partial_fun2_V x y:
  inc (J x y) (source f) -> Vf (partial_fun2 f y) x = Vf f (J x y).
Proof.
move=> Js; apply: LfV => //; first by apply: partial_fun2_axioms.
apply /iim_graph_P; ex_tac; fprops.
Qed.

End Funtion_two_args.

(** Product of two functions *)

Definition ext_to_prod u v :=
  Lf(fun z=> J (Vf u (P z))(Vf v (Q z)))
  ((source u) \times (source v))
  ((target u)\times (target v)).

Notation "f \ftimes g" := (ext_to_prod f g) (at level 40).  

Section Ext_to_prod.
Variables u v: Set.
Hypothesis (fu: function u) (fv: function v).

Lemma ext_to_prod_f:  function (u \ftimes v).
Proof. 
apply: lf_function => t /setX_P [_ px py]; apply: setXp_i; fprops.
Qed. 

Lemma ext_to_prod_V2 c:
  inc c ((source u) \times (source v)) ->
  Vf (u \ftimes v) c = J (Vf u (P c)) (Vf v (Q c)).
Proof. 
move => h;rewrite LfV // => t /setX_P [_ px py]; apply: setXp_i; fprops.
Qed.

Lemma ext_to_prod_V  a b:
  inc a (source u) -> inc b (source v)->
  Vf (u \ftimes v) (J a b) = J (Vf u a) (Vf v b).
Proof. 
by move => asu bsv; rewrite ext_to_prod_V2; aw; trivial; apply: setXp_i.
Qed.

Lemma ext_to_prod_s: source (u \ftimes v) = source u \times source v.
Proof. by rewrite/ext_to_prod; aw. Qed.

Lemma ext_to_prod_r:
 Imf (u \ftimes v) = (Imf u) \times (Imf v).
Proof.
have fe: (function (u \ftimes v)) by apply:ext_to_prod_f.
set_extens t.
  move/(Imf_P fe) => [x ]; rewrite (ext_to_prod_s) => xs ->.
  rewrite (ext_to_prod_V2 xs); move/setX_P:xs => [_ px qx].
  apply /setXp_i; Wtac.
move/setX_P => [pt  /(Imf_P fu) [x xsu xp] /(Imf_P fv) [y ysv yp]].
apply/(Imf_P fe);rewrite ext_to_prod_s; exists (J x y);first by fprops.
by rewrite (ext_to_prod_V)// - pt xp yp.
Qed.

End Ext_to_prod.

Hint Resolve  ext_to_prod_f: fprops.


(** If the two functions are  injective, surjective, bijective, 
so is the product. The inverse of the product is trivial *)

Lemma ext_to_prod_fi u v:
  injection u -> injection  v -> injection (u \ftimes v).
Proof. 
move=> [fu iu] [fv iv]; split; fprops.
rewrite /ext_to_prod; aw.
move => x y xs ys /=; rewrite ext_to_prod_V2 // ext_to_prod_V2 //.
move: xs ys => /setX_P [px pxs qxs] /setX_P [py pys qys] eq.
apply: pair_exten =>//. 
 by apply: iu=>//; apply: (pr1_def eq).
by apply: iv=>//; apply: (pr2_def eq).
Qed.

Lemma ext_to_prod_fs u v:
  surjection u -> surjection v -> surjection (u \ftimes v).
Proof. 
move=>  [fu su] [fv sv].
split; first by fprops.
move=> y; rewrite ext_to_prod_s  /ext_to_prod; aw.
move/setX_P=> [py ptu qtv].
move: (su _ ptu)=> [pv prv prw].
move: (sv _ qtv)=> [qv qrv qrw]. 
exists (J pv qv); fprops.
by rewrite ext_to_prod_V // - prw - qrw py.
Qed.

Lemma ext_to_prod_fb u v:
  bijection u -> bijection  v -> bijection (u \ftimes v).
Proof.  
move => [p1 p2] [p3 p4]. 
split; [by apply: ext_to_prod_fi | by apply: ext_to_prod_fs ].
Qed.


Lemma ext_to_prod_bp A B C D f g:
  bijection_prop f A B -> bijection_prop g C D ->
  bijection_prop (f\ftimes g) (A \times C) (B\times D).
Proof.
move =>[bf <- <-][bg <- <-].
by move:(ext_to_prod_fb bf bg) => bb; split => //; rewrite/ext_to_prod; aw.
Qed.


Lemma ext_to_prod_inverse u v:
  bijection u -> bijection  v-> 
  inverse_fun (u \ftimes v) = 
  (inverse_fun u) \ftimes (inverse_fun v).
Proof.
move=> bu bv.
have Ha:bijection (u \ftimes v) by apply: ext_to_prod_fb.
have Hb:function (inverse_fun u) by  apply: bijective_inv_f. 
have Hc:function (inverse_fun v) by  apply: bijective_inv_f. 
apply: function_exten; fprops; try solve [rewrite /ext_to_prod; aw;trivial].
  by apply: bijective_inv_f. 
move=> x.
rewrite /ext_to_prod ifun_s lf_target; move/setX_P=>[xp pxu qxv].
rewrite ext_to_prod_V2 //; last apply:setX_i; aw;fprops.
have p1: (inc (Vf (inverse_fun u) (P x)) (source u)).
  by rewrite -ifun_t; Wtac; rewrite ifun_s.
have p2: (inc (Vf (inverse_fun v) (Q x)) (source v)).
  by rewrite -ifun_t; Wtac; rewrite ifun_s.
have eq: x = Vf  (ext_to_prod u v) (J (Vf (inverse_fun u) (P x)) (Vf 
     (inverse_fun v)(Q x))).
  rewrite ext_to_prod_V //; try fct_tac.
  rewrite inverse_V // inverse_V //.
by rewrite {1} eq inverse_V2 // /ext_to_prod; aw;apply: setXp_i.
Qed.


Lemma ext_to_prod_identity x y:
  (identity x) \ftimes (identity y) = identity (x \times y).
Proof.
move:(identity_f x) (identity_f y) => fx fy. 
apply: (function_exten (ext_to_prod_f fx fy) (identity_f (x\times y))).
- by rewrite /ext_to_prod; aw.
- by rewrite /ext_to_prod; aw.
- rewrite {1} /ext_to_prod;aw => i ip /=; rewrite ext_to_prod_V2; aw;trivial.
  by move /setX_P: (ip) => [ha hb hc]; rewrite !idV; aw.
Qed.


Lemma Eq_mul_inv A B C D: A \Eq B -> C \Eq D ->
 (A \times C) \Eq (B \times D).
Proof.
move => [f [bf <- <-]] [f' [bf' <- <-]].
move:(ext_to_prod_fb bf bf') => h.
by exists  (f \ftimes f'); split => //; rewrite /ext_to_prod; aw.
Qed.

(** Composition of products *)


Lemma ext_to_prod_coP f g f' g':
   g \coP f -> g' \coP f' -> (g \ftimes g') \coP (f \ftimes f').
Proof.
move => [ha hb hc][ra rb rc]; split => //.
- by apply:ext_to_prod_f.
- by apply:ext_to_prod_f.
- by rewrite /ext_to_prod; aw; rewrite hc rc.
Qed.



Lemma compose_ext_to_prod2 u v u' v':
  u' \coP u -> v' \coP v -> 
  (u'\ftimes  v') \co (u \ftimes v) = (u' \co  u) \ftimes (v' \co v).
Proof. 
move=> cuu cvv.
move:(ext_to_prod_coP cuu cvv) => cee.
have fcu: (function (u' \co u)) by fct_tac.
have fcv: (function (v' \co v)) by fct_tac. 
apply: function_exten.
- fct_tac.
- fprops.
- by rewrite/ext_to_prod;aw.
- by rewrite/ext_to_prod;aw.
- aw; move => x xs1; move: (xs1); rewrite ext_to_prod_s => xs.
  move:(xs); move/setX_P => [xp pxs qxs].
  have res1: inc (Vf (ext_to_prod u v) x) (product (source u') (source v')).
    have aux: (product (source u') (source v')= target(ext_to_prod u v)).
      by move:cuu => [_ _ ->]; move: cvv => [_ _ ->]; rewrite /ext_to_prod; aw. 
    Wtac; fct_tac.
  rewrite compfV // ext_to_prod_V2 //; try fct_tac.  
  rewrite ext_to_prod_V2 //; try fct_tac. 
  by rewrite ext_to_prod_V2 //; [ rewrite !compfV //; aw | aw].
Qed.


(** Canonical decomposition of a function *)


Lemma canonical_decomposition1 f
  (g:= restriction_to_image f)
  (i := canonical_injection (Imf f) (target f)):
  function f ->
  [/\ i \coP g, f = i \co g, injection i, surjection g &
  (injection f -> bijection g )].
Proof. 
move=> ff.
move: (restriction_to_image_fs ff); rewrite -/g => sg.
have Ha:sub (Imf f) (target f) by apply: Imf_Starget.
have ii: injection i by apply: ci_fi.
have  cig: (i \coP g).
   by split;try fct_tac; rewrite corresp_t corresp_s ImfE.
split => //.
  apply: function_exten=>//; aw; try fct_tac; rewrite ?corresp_s ? corresp_t //.
  move => x xsf. 
  have ra:= (restriction_to_image_axioms ff).
  have xsg:  inc x (source g) by  rewrite corresp_s.
  rewrite compfV // restriction2_V // ci_V //; Wtac.
apply: restriction_to_image_fb.
Qed.


End Bfunction. 

Export Bfunction.

