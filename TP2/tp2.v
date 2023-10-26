Require Import Arith.
Lemma beq_nat_true : forall n m : nat, (n =? m) = true -> n = m.
Proof. apply Nat.eqb_eq. Qed.
  

(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)
(* AVOIR SON COURS SOUS LES YEUX *)


(**********************************************************************)
(* Un prÃ©dicat particulier : =                                        *)
(**********************************************************************)
(* Un prÃ©dicat = est dÃ©jÃ  dÃ©fini en Coq. On peut considÃ©rer qu'il s'agit de la plus petite relation rÃ©flexive *)
(* C'est un inductif avec une seule rÃ¨gle de construction : pour tout x on construit  x=x. *)
(* La rÃ¨gle d'introduction de = est "reflexivity". *)

Lemma egalite : 4=4.
Proof.
Qed.

(* Lorsqu'on a une Ã‰GALITÃ‰ x = y dans une hypothÃ¨se, disons Heq, on peut remplacer
- dans le but
  + tous les x libres par des y avec
    rewrite -> Heq.
  + tous les y libres par des x avec
    rewrite <- Heq.
- dans une hypothÃ¨se, disons H,
  + tous les x libres par des y avec
    rewrite -> Heq in H.
  + tous les y libres par des x avec
    rewrite <- Heq in H.
 *)

Lemma ex_rewrite (x : nat)  : 1 + (x + 3) = 6 -> 1 + (x + 3) = 1 + x + 3  -> 1 + (1 + x + 3) = 1 + 6.
Proof.
Qed.

(* En Coq des CONSTRUCTEURS DIFFÃ‰RENTS donnent des TERMES DIFFÃ‰RENTS.  *)
(* Si en hypothÃ¨se on trouve le prÃ©dicat d'Ã©galitÃ© avec deux membres diffÃ©rents alors on peut achever la preuve directement avec
"discriminate". *)
Lemma hyp_egal_diff : 3=4 -> False.
Proof.
(* cette formule vient de l'introduction de la flÃ¨che *)
intro Habs.
(* on voit que l'hypothÃ¨se Habs est une Ã©galitÃ© avec deux constructeurs diffÃ©rents, on finit la preuve directement avec "discriminate". *)
discriminate.
Qed.


(**********************************************************************)
(* STRUCTURE DE BASE DES LISTES (FINIES) D'ENTIERS                    *)
(**********************************************************************)


(*On rappelle que les objets de type nat sont dÃ©finis inductivement de faÃ§on similaire Ã  
Inductive entiers : Set :=
  | O : entiers
  | S : entiers -> entiers.
*)

Print nat.

(* On dispose donc d'un principe d'induction nat_ind, construit Ã  peu prÃ¨s comme vu en cours *)
Check nat_ind.
(* Si on omet le "forall P" qui n'est PAS du premier ordre, on se retrouve bien avec deux branches :
   - une branche qui demande de prouver sur le cas de base des nat, c'est-Ã -dire 0
   - une branche qui demande de prouver sur un nat construit par S Ã  partir d'un nat sur lequel on sait dÃ©jÃ  prouevr la propriÃ©tÃ©
   On peut en dÃ©duire la propriÃ©tÃ© sur tout nat obtenu par 0 et S. *)



(* EN COQ : l'application de la tactique "induction" sur un nom
   d'entier produira donc DEUX sous-buts (il y a bien 2 rÃ¨gles de
   construction des entiers...) :
  - Le sous-but correspondant au cas de bas O, 
  - Le sous-but correspondant au cas inductif oÃ¹ l'hypothÃ¨se d'induction apparaÃ®t
    dans le contexte.

COMME ON SAIT que Ã§a va mettre deux nouvelles choses dans la branche de droite et rien de nouveau dans celle de gauche on peut mÃªme nommer directement :
   induction "n" as [ | "m" "Hyp_Ind_m"].
oÃ¹ n est dans le cas de droite l'entier S m avec comme hypothÃ¨se d'induction que la propriÃ©tÃ© est vraie pour m (hypothÃ¨se nommÃ©e ici Hyp_Ind_m).  
 *)


(* On dÃ©finit les listes de nat *)
Inductive nlist : Set :=
| nnil : nlist                  
| ncons : nat -> nlist -> nlist. 

(* ... avec des notations confortables *)
Infix "::" := ncons.
Notation "[]" := nnil.

(* Vous avez vu la gÃ©nÃ©ration des principes d'induction ? *)
Check nlist_ind.
(* C'est tout Ã  fait similaire au cas des nat.
   Si on omet le "forall P" qui n'est PAS du premier ordre, on se retrouve bien avec deux branches :
   - une branche qui demande de prouver sur le cas de base des listes
   - une branche qui demande de prouver sur une liste construite par :: Ã  partir d'une liste sur laquelle on sait dÃ©jÃ  prouevr la propriÃ©tÃ©
   On peut en dÃ©duire la propriÃ©tÃ© sur toute liste obtenue par [] et ::. *)





(******************************************************************************)
(* FONCTIONS NON-RECRUSIVES SUR LES TYPES INDUCTIFS                           *)
(******************************************************************************)

(* Si on n'a pas besoin d'hypothÃ¨se d'induction, il est en gÃ©nÃ©ral suffisant de faire une Ã©tude par cas, 
   c'est-Ã -dire un destruct de l'objet Ã©tudiÃ© *)

Inductive Alphabet : Type :=
| a : Alphabet
| b : Alphabet.

(* Prouvez les correction et complÃ©tude de la fonction comp_alphabet de votre TP de LIFLF, c'est-Ã -dire qu'elle retourne true si et seulement si ses deux paramÃ¨tres sont Ã©gaux
  - on procÃ¨de par cas sur les deux paramÃ¨tres
  - on peut Ãªtre amenÃ© Ã  faire des calculs (avec simpl dans le but ou simpl in toto dans l'hypothÃ¨se toto. *)
Definition comp_alphabet (x : Alphabet) (y : Alphabet) : bool := (* mettez votre code ici *)
.

Theorem comp_alphabet_ssi (x : Alphabet) (y : Alphabet) : (comp_alphabet x y = true -> x = y) /\ (x = y -> comp_alphabet x y = true).
Proof.
Qed.



(* On rappelle la fonction de comparaison sur les option nat codÃ©e en LIFLF *)
Definition comp_option_nat (x y: option nat) : bool :=
match x with
  | None => match y with | None => true | Some toto => false end
  | Some n => match y with | Some m => Nat.eqb n m | None => false end
end.



(* EN COQ : si on a une hypothÃ¨se H : forall x, P(x) on peut la
 spÃ©cialiser en une nouvelle hypothÃ¨se pour une certaine valeur de x,
 disons n. Pour celÃ  on invoque "pose (H n) as nouveauH".  On crÃ©e
 alors une nouvelle hypothÃ¨se qui s'appelle nouveauH qui est un cas
 particulier de H, celui oÃ¹ x vaut n : nouveauH : P(n)
*)


(* Montrer que (comp_option_nat x y) retourne true SEULEMENT SI x=y. 
   on utilisera le thÃ©orÃ¨me
   beq_nat_true: forall n m : nat, Nat.eqb n  m = true -> n = m 
   qu'on spÃ©cialisera aux bons paramÃ¨tres "n_fixe", "m_fixe" avec 
   pose (beq_nat_true "n_fixe" "m_fixe") as "nom_de_la_nouvelle_hypothÃ¨se".
   
  ATTENTION : Nat.eqb e1 e2 s'Ã©crit aussi e1 =? e2

*)
Theorem comp_option_nat_seulement_si (x : option nat) (y : option nat) : comp_option_nat x y = true -> x = y.
Proof.
Qed.



(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES ENTIER                           *)
(******************************************************************************)

(* Exercice : montrer que la fonction plus appliquÃ©e Ã  0 et un x quelconque retourne x. *)
(* La dÃ©finition de plus est rÃ©cursive sur le paramÃ¨tre de gauche, donc pas de problÃ¨me ici, c'est juste un calcul (simpl) *)
Lemma plus_Z_l (x : nat) : plus 0 x = x.
Proof.
Qed. 

(* Exercice : montrer que la fonction plus appliquÃ©e un x quelconque et 0 retourne x. *)
(* Mmmh lÃ  il faut travailler par induction sur x... *)
(* on utilise "induction x as..." qui invoque la rÃ¨gle nat_ind. *)
Lemma plus_Z_r (x : nat) : plus x 0 = x.
Proof.
Qed. 



(******************************************************************************)
(* FONCTIONS RECURSIVES ET INDUCTION SUR LES LISTES                           *)
(******************************************************************************)


(* Exercice *)
(* DÃ©finir "concat" la fonction de concatÃ©nation de deux listes l1 et l2 (par rÃ©cursion sur l1) *)
Fixpoint concat (l1 l2 : nlist) : nlist := (* Ã©crire votre code ici *)
  end.

(* On note ++ en notation infix pour la concatenation *)
Infix "++" := concat.

(* VU EN COURS : fonction de longueur des listes                              *)
Fixpoint length (l : nlist) : nat :=
  match l with
  | []     => 0 
  | x :: l => S(length l) 
  end.

(* Exercice : montrer que la fonction retourne 0 SEULEMENT SI la liste
   est vide *)
Lemma length_zero_seulement_si_vide (l : nlist) : length l = 0 -> l=[].
Proof.
Qed.



(* Exercice : montrer que la fonction appliquÃ©e Ã  la concatÃ©nation de
deux listes quelconques l1 l2 retourne la somme des applications de
cette fonction Ã  chacune des deux listes.*)
Lemma length_of_concat (l1 : nlist) (l2 : nlist) : length (l1 ++ l2) = length l1 + length l2.
Proof.
Qed.



(* QUANTIFICATION UNIVERSELLE *)
(* RÃ¨gle d'introduction du quantificateur universel *)
(* La tactique utilisÃ©e pour la rÃ¨gle d'introduction de l'universel est intro "nom de la variable gÃ©nÃ©rique". *)

(* Prouver que pour tout nat x et toute liste de nat l,
la liste vide n'est pas obtenue par l'ajout de x en tÃªte de l. *)
Lemma nil_neq_cons : forall (x:nat), forall (l:nlist), [] = x :: l -> False.
Proof.
  intro un_element_general.
  intro une_liste_generale.
  intro Habsurde.
  (* poursuivre la preuve *)
Qed.



(* Exprimer et montrer que pour tout Ã©lÃ©ment x et toutes listes l1 et
l2, ajouter x en tÃªte de la concatÃ©nation de l1 et l2 est
la mÃªme chose que concatÃ©ner l1 avec x en tÃªte et l2. *)
(* pas de difficultÃ©, c'est juste un pas de calcul (simpl). *)

Lemma concat_cons : False
Proof.
Qed.

(* Eprimer et montrer maintenant que pour toute liste l1, concatÃ©ner Ã  l1 la liste vide renvoie exactement la liste l1. *)
(* Comme on a dÃ©fini concat par rÃ©cursion sur le premier paramÃ¨tre, il va falloir une induction... *)
Lemma concat_nil_r : False
Proof.
Qed.

