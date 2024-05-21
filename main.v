Require Import Setoid.
Require Import Lia.




Record GroupTheo : Type := groupTheo
  { Gt : Set; (* nosnik *)
    opt : Gt -> Gt -> Gt; (* operacja *)
    assoct : forall(x y z : Gt), opt (opt x y) z = opt x (opt y z);
    neutt := exists( e : Gt), forall(x : Gt), opt e x = x /\ opt x e = x;
    invt := forall(e : Gt), (forall(x : Gt), opt e x = x /\ opt x e = x )->  forall(x : Gt), exists( y : Gt) , opt x y = e /\ opt y x  = e; 
  }.




(* Jednoznaczność elementu neutralnego - krótszy zapis*)
Definition idPro (g : GroupTheo ) (e : Gt g) := (forall(x : Gt g), opt g e x = x /\ opt g x e = x).


Theorem exOnlyOne : forall (g : GroupTheo), forall( e f : Gt g), (idPro g e /\ idPro g f) -> e = f.
Proof.  
  unfold idPro.
  intros.
  destruct H.
  specialize H with (x := f) .
  specialize H0 with (x := e) .
  destruct H, H0.
  rewrite <- H0.
  trivial.
Qed.



(* Jednoznaczność odwrotności - krótszy zapis  *)
Definition invPro (g : GroupTheo) (e y : Gt g):= idPro g e /\ ( forall(x : Gt g) ,( opt g x y = e /\ opt g y x  = e)).


Theorem exOnlyOneInv : forall( g : GroupTheo), forall (e y1 y2 x : Gt g), idPro g e /\ invPro g e y1 /\ invPro g e y2 -> y1 = y2.
(* Pomysł dowodu :*)
(* y1 =  y1 <*> e = y1 <*> (x <*> y2) = (y1 <*> x) <*> y2 = e <*> y2 = y2) *)
Proof.
  unfold invPro.
  unfold idPro.
  intros.
  destruct H.
  destruct H0.
  destruct H0, H1.
  specialize H with (x := y1) .
  destruct H.
  specialize H0 with (x := y2) .
  destruct H0.
  rewrite <- H4.
  rewrite <- H0.
  specialize H2 with (x := x).
  specialize H3 with (x := x).
  destruct H2, H3.
  rewrite <- H3 at 1.
  rewrite <- H6 at 1.
  rewrite (assoct).
  trivial.
Qed.

(* Definicja grupy z uwzględnieniem jednoznaczności elementu e oraz jednoznaczności odwrotności *)
Record Group : Type := group
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    inv : G -> G;
    e : G;
  
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    id :  forall(x : G), op e x = x /\ op x e = x ;
    inverse :  forall(x : G), op x (inv x) = e /\ op (inv x) x  = e ;
  }.


  

Record AbelianGroup : Type := aGroup 
  {
    abelGr : Group;
    abelComm : forall (x y : G abelGr), op abelGr  x y = op abelGr  y x;
  }.



Notation " x <* g *> y" := (op g x y) (at level 50 ).

Theorem pPowerGivesAbelian: forall (g : Group), forall( x y : G g), ( forall (p : G g),  p <* g *>  p = e g ) ->  x <* g *>  y = y  <* g *>  x.
(*  Idea dowódu
xy=(yy)xy(xx)=y(yxyx)x=yx.
 *)
Proof.
  intros.
  specialize H with (p := x) as X.
  specialize H with (p := y) as Y.
  pose (id_prop := id g). (* Wprowadzi nam własność id g do założeń *)
  specialize id_prop with (x := x) as idX.
  specialize id_prop with (x := y) as idY.
  destruct idX, idY.
  rewrite <- H0 at 1.
  rewrite <- H3 at 1.

  rewrite <- Y at 1.
  rewrite <- X at 1.
  (* Wykorzystywanie łączności *)
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (x := y) (y := y) (z := x) as assoc_y.
  rewrite assoc_y.
  specialize assoc_prop with (x := y) (y := x) (z := x) as assoc_x.
  rewrite <- assoc_x.
  specialize assoc_prop with (x := (y <* g *> (y <* g *> x))) (y := (y <* g *> x)) (z := x) as assoc_mul.
    rewrite <- assoc_mul.
    specialize assoc_prop with (x := y) (y :=  (y <* g *> x)) (z := (y <* g *> x)) as assoc_doub.
    rewrite assoc_doub.
    specialize H with (p := (y <* g *> x)) as YX.
  rewrite YX at 1.
  rewrite H3.
  trivial.
Qed.




    


