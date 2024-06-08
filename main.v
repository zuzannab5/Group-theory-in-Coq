Require Import Setoid.
Require Import Lia.

(* Typ grupy teoretycznej - zgodnie z definicją grupy z Bagińskiego *)
Record GroupTheo : Type := groupTheo
  { Gt : Set; (* nosnik *)
    opt : Gt -> Gt -> Gt; (* operacja *)
    assoct : forall(x y z : Gt), opt (opt x y) z = opt x (opt y z);
    neutt := exists( e : Gt), forall(x : Gt), opt e x = x /\ opt x e = x;
    invt := forall(e : Gt), (forall(x : Gt), opt e x = x /\ opt x e = x )->  forall(x : Gt), exists( y : Gt) , opt x y = e /\ opt y x  = e; 
  }.

(* Jednoznaczność elementu neutralnego - krótszy zapis*)
Definition idPro (g : GroupTheo ) (e : Gt g) := (forall(x : Gt g), opt g e x = x /\ opt g x e = x).

(* Twierdzenie, że istnieje dokładnie jeden element neutralny *)
Theorem exOnlyOneE : forall (g : GroupTheo), forall( e f : Gt g), (idPro g e /\ idPro g f) -> e = f.
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

(* Twierdzenie, że dla dowolnego elementu istnieje jeden element odwrotny*)
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

(* Definicja grupy z uwzględnieniem jednoznaczności elementu neutralnego oraz jednoznaczności odwrotności *)
Record Group : Type := group
  { G : Set; (* nosnik *)
    op : G -> G -> G; (* operacja *)
    inv : G -> G;
    e : G;
  
    assoc : forall(x y z : G), op (op x y) z = op x (op y z);
    id :  forall(x : G), op e x = x /\ op x e = x ;
    inverse :  forall(x : G), op x (inv x) = e /\ op (inv x) x  = e ;
  }.

Notation " x <* g *> y" := (op g x y) (at level 50).

Section Subgroup.

Variable H : Group.

(* Defininicja podgrupy *)
Record SubGroup (K : H.(G) -> Prop) : Prop := (*Zapis H.(G) oznacza odwołanie się do pola G rekordu H typu Group*)
{ 
  sub_inv : forall x, K x -> K (H.(inv) x); 
  sub_op : forall x y, (K x /\ K y) -> K (H.(op) x y)
}.

End Subgroup.

(*  2 definicja podgrupy *)
Inductive In (g: Group) : Type := inSet (a : G g) | notInSet (b : G g).

Record SubG := subGroup
{
  Gr : Group;
  isInH : G Gr -> In Gr; 
  notEmpty : exists(x : G Gr), isInH x = inSet Gr x;
  cInv : forall(x : G Gr), isInH x = inSet Gr x -> isInH (inv Gr x) = inSet Gr (inv Gr x) ;
  cOp : forall(x y : G Gr), isInH x = inSet Gr x  /\  isInH y = inSet Gr y -> isInH (x <* Gr *> y) = inSet Gr (x <* Gr *> y) ;
}.




(* Definicja grupy abelowej *)
Record AbelianGroup : Type := aGroup 
  {
    abelGr : Group;
    abelComm : forall (x y : G abelGr), x <* abelGr *> y = y <* abelGr *> x;
  }.


(*lematy dające zachowanie równości przy mnożeniu przez ten sam element*)

Lemma lmult_a: forall (g : Group), forall (a b c : G g), b = c -> a <* g *> b = a <* g *> c.
  intros; 
  rewrite H; 
  auto.
Qed.

Lemma rmult_a: forall (g : Group), forall (a b c : G g), b = c -> b <* g *> a = c <* g *> a.
  intros; 
  rewrite H; 
  auto.
Qed.


(*Prawo skracania z lewej strony*)
Theorem cancelL: forall (g : Group), forall (a b c : G g), a <* g *> b = a <* g *> c -> b = c.
Proof.
  intros.
  pose (inv_prop := inverse g). (*wprowadzamy do założeń id g, assoc g i inv g*)
  pose (id_prop := id g).
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (x := inv g a)(y := a)(z:=b) as AssocB.
  specialize assoc_prop with (x := inv g a)(y := a)(z:=c) as AssocC.
  specialize inv_prop with (x := a) as invA.
  specialize id_prop with (x := b) as idB.
  specialize id_prop with (x := c) as idC.
  destruct idB, idC.
  rewrite <- H0, <- H2.
  destruct invA.
  rewrite <- H5.
  rewrite AssocB.
  rewrite AssocC.
  apply (lmult_a).
  trivial.
Qed.



(*Prawo skracania z prawej strony*)
Theorem cancelR: forall (g : Group), forall (a b c : G g), b <* g *> a = c <* g *> a -> b = c.
Proof.
  intros.
  pose (inv_prop := inverse g). (*wprowadzamy do założeń id g, assoc g i inv g*)
  pose (id_prop := id g).
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (z := inv g a)(y := a)(x:=b) as AssocB.
  specialize assoc_prop with (z := inv g a)(y := a)(x:=c) as AssocC.
  specialize inv_prop with (x := a) as invA.
  specialize id_prop with (x := b) as idB.
  specialize id_prop with (x := c) as idC.
  destruct idB, idC.
  rewrite <- H1, <- H3.
  destruct invA.
  rewrite <- H4.
  rewrite <- AssocB.
  rewrite <- AssocC.
  apply (rmult_a).
  trivial.
Qed.


(*Przepisanie jednoznaczności elementu odwrotnego na typ Group*)
Theorem inv_uniq: forall (g : Group), forall (a b: G g), a <* g *> b = e g -> b = inv g a.
Proof.
  intros.
  apply (cancelL g a b (inv g a)).
  pose (inv_prop := inverse g).
  specialize inv_prop with (x := a) as invA.
  destruct invA.
  rewrite H0.
  trivial.
Qed.

(*Twierdzenie o tym, że (a^(-1))^(-1)=a*)
Theorem InvInvAIsA: forall (g : Group), forall (a : G g), inv g (inv g a) = a.
Proof.
  intros.
  pose (inv_prop := inverse g).
  specialize inv_prop with (x := a) as invA.
  destruct invA.
  apply inv_uniq in H0.
  symmetry.
  trivial.
Qed.



(*Twierdzenie o tym, że (ab)^-1=b^-1*a^-1 *)
Theorem InvABEqInvBInvA: forall (g : Group), forall (a b: G g), inv g (a <* g *> b) = inv g b <* g *> inv g a.
Proof.
  intros.
  apply (cancelL g (a <* g *> b)).
  rewrite <- (assoc g).
  pose (inv_prop := inverse g).
  specialize inv_prop with (x := a <* g *> b) as invAB.
  destruct invAB.
  rewrite H.
  specialize inv_prop with (x := b) as invB.
  destruct invB.
  specialize inv_prop with (x := a) as invA.
  destruct invA.
  pose (assoc_prop := assoc g).
  specialize assoc_prop with (x := a)(y := b)(z:=inv g b) as AssocBinv. 
  rewrite AssocBinv.
  rewrite H1.
  pose (id_prop := id g).
  specialize id_prop with (x := a) as idA.
  destruct idA.
  rewrite H6.
  rewrite H3.
  trivial.
Qed.




(* Dowód twierdzenia, że jeśli dla każdego x, y, x^2 = e, to x * y = y * x*)
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




Section Z4_Group.

(* Definiujemy typ dla Z4 *)
Inductive Z4 : Type := z0 | z1 | z2 | z3.

(* Definiujemy dodawanie modulo 4 *)
Definition add_Z4 (a b : Z4) : Z4 :=
  match a, b with
  | z0, x => x
  | x, z0 => x
  | z1, z1 => z2
  | z1, z2 => z3
  | z1, z3 => z0
  | z2, z1 => z3
  | z2, z2 => z0
  | z2, z3 => z1
  | z3, z1 => z0
  | z3, z2 => z1
  | z3, z3 => z2
  end.

(* Element neutralny dla dodawania *)
Definition e_Z4 : Z4 := z0.

(* Definiujemy operację odwrotności *)
Definition inv_Z4 (a : Z4) : Z4 :=
  match a with
  | z0 => z0
  | z1 => z3
  | z2 => z2
  | z3 => z1
  end.
  
(* Własność łączności *)
Lemma add_assoc : forall (x y z : Z4), add_Z4 x (add_Z4 y z) = add_Z4 (add_Z4 x y) z.
Proof.
  intros x y z.
  destruct x, y, z;
  simpl;
  reflexivity.
Qed.

(* Lewostronne działanie elementu neutralnego *)
Lemma add_e_l : forall (x : Z4), add_Z4 e_Z4 x = x.
Proof.
  intros.
  destruct x; 
  simpl; 
  reflexivity.
Qed.

(* Prawostronne działanie elementu neutralnego *)
Lemma add_e_r : forall (x : Z4), add_Z4 x e_Z4 = x.
Proof.
  intros.
  destruct x; 
  simpl; 
  reflexivity.
Qed.

(* Lewostronna odwrotność *)
Lemma add_inv_l : forall (x : Z4), add_Z4 (inv_Z4 x) x = e_Z4.
Proof.
  intros.
  destruct x; 
  simpl; 
  reflexivity.
Qed.

(* Prawostronna odwrotność *)
Lemma add_inv_r : forall (x : Z4), add_Z4 x (inv_Z4 x) = e_Z4.
Proof.
  intros.
  destruct x; 
  simpl; 
  reflexivity.
Qed.

(* Dowód, że Z_4 jest grupą, co jest łącznym wynikiem powyższych lematów *)
Theorem Z4_is_group : forall (x y z : Z4), add_Z4 x (add_Z4 y z) = add_Z4 (add_Z4 x y) z /\ add_Z4 e_Z4 x = x /\ 
add_Z4 x e_Z4 = x /\ add_Z4 (inv_Z4 x) x = e_Z4 /\ add_Z4 x (inv_Z4 x) = e_Z4.
Proof.
  intros.
  split.
  apply add_assoc.
  split.
  apply add_e_l.
  split.
  apply add_e_r.
  split.
  apply add_inv_l.
  apply add_inv_r.
Qed.


(*Jeszcze zostało udowodnić, że Z_2 jest podgrupą Z_4*)


End Z4_Group.
    


