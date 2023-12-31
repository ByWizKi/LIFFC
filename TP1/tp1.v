(* LES SEULES COMMANDES AUTORISÃ‰ES SONT CELLES DÃ‰CRITES DANS CE FICHIER. *)

(* Les indications entre  ne sont pas Ã  recopier, elles indiquent
   juste que vous avez Ã  mettre un nom Ã  cet endroit. *)


(* On introduit les variables propositionnelles avec lesquelles 
   on va travailler par la suite *)
Context (P Q R A Z J F M S T: Prop).

(**********************************************************************)
(* Exercice 1 LA FLÃˆCHE  ***********************)

(* - axiome : assumption
   - introduction de la flÃ¨che : intro nom qu'on donne Ã  l'hypothÃ¨se 
   - Ã©limination de la flÃ¨che : apply nom de l'hypothÃ¨se utilisÃ©e *)
   
Theorem exercice_1a: P -> (P -> Q) -> Q.
intro H1.
intro H2.
apply H2. 
assumption.
Proof.
Qed.


Theorem exercice_1b: (P -> Q) -> (Q -> R) -> (P -> R).
intro H1.
intro H2.
intro H3.
apply H2.
apply H1.
assumption.
Proof.
Qed.

(* Exercice 2 LE ET  ***********************)
(* Une variante de la question prÃ©cÃ©dente avec /\ *)
(* - dÃ©composition du /\ en hypothÃ¨se : destruct nom de l'hypothÃ¨se avec /\ as [ nom gauche nom droite ]
*)
Theorem exercice_2a: (P -> Q) /\ (Q -> R) -> (P -> R).
intro H.
intro H0.
apply H.
destruct H.
apply H.
assumption.
Proof.
Qed.

(* - introduction du /\ : split *)
(* On obtient bien deux sous-buts *)
Theorem exercice_2b : P -> (Q -> P /\ Q).
intro H.
intro H2.
split.
assumption.
assumption.
Proof.
Qed.
  
(* Exercice 3 LE OU  ***********************)
(* introduction du ou :
   - depuis la droite : right
   - depuis la gauche : left

   decomposition du \/ en hypothÃ¨se : destruct nom de l'hypothÃ¨se avec \/ as [ nom gauche | nom droite ]
   notez le | qui sÃ©pare les sous-buts. *)

Theorem exercice_3a: (P \/ Q) -> (Q \/ P).
intro H1.
left.
destruct H1 as [ H2 | H3 ].
destruc
Proof.
Qed.

(* Ã€ partir de maintenant on nommera SYSTÃ‰MATIQUEMENT les hypothÃ¨ses qui
apparaissent dans les destruct avec "as" et suivant le nombre de sous-buts *)
(* ---------------------------------------------------------------------*)


(* zÃ©ro constructeur *)
Print False. 
(* un seul constructeur car une seule rÃ¨gle d'intro *)
Print and.
(* deux constructeurs car deux rÃ¨gles d'intro*)
Print or.  

(* destruct donne bien un sous but par constructeur *)
(* On remarque que comme False n'a aucun constructeur : le destruct
rÃ©soud le but *)
Theorem ex_falso_quodlibet : False ->  P.
Proof.
Qed.

(** un peu difficile **)
(* Plus gÃ©nÃ©ralement, la tactique exfalso remplace tout but par False. *)
(* Si on peut dÃ©duire False des hypothÃ¨ses, c'est alors gagnÃ© ! *)

Theorem ex_falso_quodlibet_Q : (A -> False) -> A -> (P \/ (Q -> Z /\ J) -> F).
Proof.
Qed.
  

(* ---------------------------------------------------------------------*)


(* Exercice 4 PREMIÃˆRE MODÃ‰LISATION  ***********************)
(* ModÃ©liser l'exercice de TD "ZoÃ© va Ã  Paris", prouver que ZoÃ© va Ã  Paris *)
(* - introduction du /\ : split
*)
Theorem zoe_va_a_paris : (A /\ J -> Z) -> (J -> A) -> (Z \/ J) -> Z.
Proof.
Qed.

(* Exercice 5 LE NOT *************************)

(* - la notation not : unfold not
   - la notation not en hypothÃ¨se : unfold not in "nom de l'hypothÃ¨se avec le ~ "
*)
Theorem exercice_5a : (~P \/ ~Q) -> ~(P /\ Q).
Proof.
Qed.
(* on voit qu'on passe son temps Ã  faire des unfold dans chacun des sous-buts, il aurait donc mieux valu *commencer* par ce unfold, avant l'introduction de la flÃ¨che *)


(* Si on a toto et ~toto dans les hypothÃ¨ses, alors le but est rÃ©solu avec "contradiction." *)
(* c'est juste un raccourci pour exfalso. apply "hypothÃ¨se avec le -> False". assumption. *)
Theorem exercice_5b : P -> ~P -> Q.
Proof.
Qed.

(**********************************************************************)
(* Exercice 6 LE TIERS-EXCLU *)

(* On introduit la rÃ¨gle de tiers-exclu. *)
Context (Tiers_exclus: forall X: Prop, X \/ ~X).

(* Pour l'utiliser, c'est-Ã -dire pour avoir deux sous buts, un avec toto en hypothÃ¨se, l'autre avec ~toto, on invoquera :
   destruct (Tiers_exclus toto) as [ "nom_hyp" | "nom_hyp ~" ].
*)


Theorem exercice_6a: ((P -> Q) -> P) -> P.
Proof.
Qed.

(* DeuxiÃ¨me modÃ©lisation *)
(* ModÃ©liser l'exercice de TD "Frodon va au Mordor", prouver que Frodon est triste *)

Theorem exercice_6b : (~F -> S) -> (S -> T) -> (F -> ~A) -> (~A -> T) -> T.
Proof.
Qed.


(* Quid de ~~P et P ? *)
Theorem exercice_6c: (~~P -> P) /\ (P -> ~~P).
(* Pour l'un des deux sens on aura besoin du tiers-exclu et, en remarquant qu'on peut dÃ©duire False des hypothÃ¨ses, de la simplification "exfalso". *)

Proof.
Qed.
