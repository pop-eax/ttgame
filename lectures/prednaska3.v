(*
Prednáška 3:
- Údajové štruktúry: Pair a List
- Logické uvažovanie o Pair a List
- Option
- Polymorfné verzie Pair, List a Option
*)

(** Import knižníc*)
From Coq Require Import String.
Open Scope string_scope.

(*===========================================*)
(**          Údajové štruktúry              **)
(*===========================================*)

(*
V tejto časti sa zoznámime s niekoľkými 
základnými údajovými štruktúrami
v prostredí Rocq, ktoré sú základom 
pre reprezentáciu dát a pre 
logické uvažovanie o programoch.

Budeme postupne preberať:
- jednoduché štruktúry ako **dvojice (pair)**,
- dynamické štruktúry ako **zoznamy (list)**,
- budeme uvažovať o týchto štruktúrach 
  formálne pomocou logických dôkazov,
- ukážeme si ich **polymorfné verzie**, 
  ktoré fungujú pre ľubovoľný typ,
- a nakoniec zavedie typ **option**, 
  ktorý slúži na reprezentáciu
  čiastočne definovaných funkcií.

Dôležitá poznámka:
- Štandardná knižnica Rocq 
  obsahuje definície základných štruktúr
  ako **pair** a **list**.
- My si ich však najprv sami zadefinujeme nanovo, 
  aby sme lepšie porozumeli princípom ich fungovania.
*)

(*===========================================*)
(**          Dvojica: pair                  **)

Module natpair.

Inductive natpair: Type :=
| pair (n m :nat).

(* 
Jediný spôsob, ako vytvoriť dvojicu prírodzených čísel 
je aplikovať konštruktor natpair na 
dva argumenty typu nat.
*)

Check (pair 2 8).

(* 
Pre extrakciu hodnôt typu natpair potrebujeme dve projekcie:
fst a snd.
*)

Definition fst (x: natpair) : nat := 
match x with
| pair n m => n
end.

Definition snd (x: natpair) : nat := 
match x with
| pair n m => m
end.

Compute (fst (pair 3 9)).
Compute (snd (pair 3 9)).
Compute (fst (pair (snd (pair 1 4)) 9)).

(* Zavedieme štandardnú notáciu pre dvojicu *)
Notation "( x , y )" := (pair x y).

Check (1,8).

(* Funkcia na prehodenie prvkov dvojice *)
Definition swap (p : natpair) : natpair :=
match p with
| pair m n => pair n m 
end. 

Compute swap (1,8).

(* 
Zavedenú štandardnú notáciu pre dvojicu je možné použiť 
aj v definíciách nových funkcií. 
*)
Definition swap' (p : natpair) : natpair :=
match p with
| (m,n) => (n,m) 
end. 

Compute swap' (1,8).

(**    Logické uvažovanie o dvojici čísel    **)

(**
Príklad: ak máme n a m, vieme okamžite ukázať, že
(n,m) = (fst (n,m), snd (n,m)).
*)

Theorem pair_reconstruction' : forall (n m : nat),
  (n,m) = (fst (n,m), snd (n,m)).
Proof.
  simpl. reflexivity. 
Qed.

(**
Avšak reflexivity už nestačí, 
ak tvrdenie napíšeme prirodzenejším spôsobom:
p = (fst p, snd p).

Tu sa totiž nedá ďalej redukovať výraz so simpl.
*)

Theorem pair_reconstruction_stuck : forall (p : natpair),
  p = (fst p, snd p).
Proof.
  simpl. (* nič sa nestane! *)
Abort.

(**
Riešením je „odkryť štruktúru“ dvojice p,
aby sa simpl dokázal pozrieť do definícií fst a snd.
Toto spravíme pomocou destruct.
*)

Theorem pair_reconstruction : forall (p : natpair),
  p = (fst p, snd p).
Proof.
  intros p.
  destruct p. (* rozloží p na jeho komponenty *)
  simpl.
  reflexivity.
Qed.

(**
Poznámka:
- Na rozdiel od destruct pri typoch ako nat 
  (kde vznikajú dva podcieľe: 0 a S n),
  pri destruct na pároch vzniká iba jeden podcieľ,
  pretože pár sa dá skonštruovať iba jediným spôsobom.
*)

End natpair.

(*===========================================*)
(**          Zoznam: list                   **)

Module natlist.

Inductive natlist : Type :=
| nil
| cons (n: nat) (l:natlist).

Check (nil).
Check (cons 1 (cons 3 nil)).

(* Zavedenie štandardnej notácie *)

Notation "[]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).
Notation "x :: l" := (cons x l) 
                     (at level 60, right associativity).

Check [].
Check [1;2;3].
Check 1::[2;3].

(* right associativity *)
Check 1::(2::(3)::nil) = 1::2::3::nil.

(** 
Priorita a asociativita operátorov v Rocq 
https://rocq-prover.org/doc/V8.18.0/
refman/language/coq-library.html
*)

(* 
at level 60 priorita operátora 
- nižšie číslo -> výššia priorita
Napr. operátory + a -  level 50, operátor * level 40
*)

Compute 1+2::5::nil. (* výsledok je [3; 5] a nie 1 + [2;5]*)

(*===========================================*)
(*Funkcie: Repeat, Length, Append, Head, Tail*)

(* Repeat: prijíma číslo n a počet count
a vracia zoznam dĺžky count, kde každý prvok je n. *)

Fixpoint repeat (n count :nat) : natlist := 
match count with
| 0 => []
| S m => n :: (repeat n m)
end.

Compute repeat 1 5.


(** length počíta počet prvkov v zozname. *)

Fixpoint length (l:natlist) : nat := 
match l with 
| [] => 0
| head :: tail => 1 + (length tail)
end.

Compute length [].
Compute length [1;2;3;5;9;44;1;1].
Compute length nil.
Compute length (cons 1 (cons 3 nil)).


(**
Funkcia append spojí dva zoznamy.  
Zadefinujeme aj infix notáciu "++".
*)

Fixpoint append (l1 l2: natlist) : natlist :=
match l1 with
| [] => l2
| head::tail => head::(append tail l2)
end.

Compute append [] [1].
Compute append [2;5;6] [1;3].

Notation "x ++ y" := (append x y) 
                     (at level 60, right associativity). 

Compute [] ++ [1].
Compute [2;5;6] ++ [1;3].

(** Funkcie head a tail *)
(* 
Všetky funkcie v Rocq musia byť úplne, 
preto štandardná implementácia týchto funkcií 
ako v jazykoch Haskell alebo Ocaml nie je možná.

Napr. volania head [] alebo tail []
sú nedefinované v Haskell alebo Ocaml a vrátia výnimku,
čo v Rocq nie je dovolené. 

Preto je nutné pridať ďalší parameter, 
ktorý bude predvolenou hodnotou pre tieto prípady
*)

Definition head (l: natlist) (default:nat) : nat := 
match l with
| [] => default
| h::t => h
end.

Definition tail (l: natlist) : natlist := 
match l with
| [] => nil
| h::t => t
end.

Compute head [] 999.
Compute head [5;6;89] 999.
Compute tail [].
Compute tail [5;6;89].

(** Funkcia reverse prehodí poradie prvkov *)
Fixpoint reverse l:natlist :=
match l with 
| [] => []
| hd::tl => (reverse tl)++[hd]
end.

Compute reverse [1;2;3;4].


(*===========================================*)
(**    Logické uvažovanie o zozname natlist **)

(** Veta: 
pripojenie prázdneho zoznamu  k inému zoznamu nezmení zoznam  *)
Theorem nil_app_l : forall l, []++l=l.
Proof.
simpl. reflexivity.
Qed.

(** 
Rocq automaticky generuje dva podcieľe: 
    - Základný prípad ([]).
    - Indukčný prípad (x::xs).

Princíp indukcie nad zoznamom:
    - Ekvivalentne jednoduchý ako indukcia nad prirodzenými číslami.
    - Base case: P([])
    - IH:        ∀x.∀xs.(P(xs) => P(x::xs))
    - Goal:      ∀l.P(l)

Úplne analogické indukcii nad prirodzenými číslami, 
len konštruktor x::xs nahrádza nasledovníka n+1.
*)

Theorem l_app_nil : forall l, l++[]=l.
Proof.
intros. induction l.
- reflexivity.
- simpl. rewrite IHl. reflexivity.
Qed.

Check pred.

(** Veta: 
    Dĺžka tail zoznamu je o jeden menej ako dĺžka zoznamu  *)
Theorem pred_l_length: forall l, 
                      pred (length l) = (length (tail l)).
Proof.
intros. destruct l.
- simpl. reflexivity.
- simpl. reflexivity.
Qed.

(** Veta: Funkcia append je neasociatívna: 
    (l1++l2)++l3 = l1++(l2++l3) *)
Theorem app_assoc: forall l1 l2 l3, 
                    (l1++l2)++l3 = l1++(l2++l3).
Proof.
intros.
Set Printing Parentheses.
induction l1.
- simpl. reflexivity.
- simpl. rewrite IHl1. reflexivity.
Qed.

(** Veta: Dĺžka zoznamu je rovná dĺžke obráteneho zoznamu *)

Lemma rev_aux: 
forall l n, S (length l) = length (l ++ [n]).
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl. rewrite IHl. reflexivity.
Qed. 

Theorem rev_length: forall l, length l = length (reverse l).
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl. rewrite IHl. apply rev_aux.
Qed. 


(** 
  Veta: Obrátenie zoznamu distribuuje cez spojenie. 

  Ak spojíme dva zoznamy a potom výsledok obrátime, 
  dostaneme rovnaký zoznam, ako keby sme najprv obrátili 
  každý zoznam osobitne a potom ich spojili v opačnom poradí.
*)

Lemma rev_app_distr : forall l1 l2,
  reverse (l1 ++ l2) = (reverse l2) ++ (reverse l1).
Proof.
  intros l1 l2.
  induction l1 as [| h t IH].
  - simpl. rewrite l_app_nil. reflexivity.
  - simpl.
    rewrite IH.
    rewrite app_assoc.
    reflexivity.
Qed.



(** Veta: Dvakrát obrátený zoznam je pôvodný zoznam *)

Compute reverse (reverse [1;2;3]) = [1;2;3].


Theorem rev_rev_l: forall l, reverse (reverse l) = l.
Proof.
intros.
induction l.
- simpl. reflexivity.
- simpl. rewrite rev_app_distr. 
  rewrite IHl. simpl. reflexivity.
Qed.


(*===========================================*)
(** Typ option a čiastočne def. funkcie     **)

(* 
  Ako už bolo spomínané, Rocq je totálny (úplný jazyk), 
  to znamená neumožnuje definovať čiastočne definované funkcie.
  Takéto obmedzenie je užitočné pre formálne dôkazy, 
  avšak v praxi vytvára problémy. 

  Príklad: Zadefinujme funkciu, ktorá vráti n-ty prvok zoznamu.
*)

Fixpoint nth_bad (l:natlist) (n:nat) : nat :=
match l with 
| []     => 0   (** zvolím nejaku predvolenú hodnotu *)
| hd::tl => match n with
           | 0 => hd
           | S m => nth_bad tl m end
end.

Compute nth_bad [] 4.
Compute nth_bad [10;12;0] 1.

Compute nth_bad [10;12;0] 2.
(** Problém: ako viem, či 0 bol n-ty prvok, 
    alebo som zvolil hodnotu mimo rozsahu zoznamu? 

    V jazykoch ktoré povoľujú čiastočne definované funkcie
    by sme použili napr. raise exception. 
*)


(** Riešenie: typ option 

  Zmeníme návratový typ funkcie [nth_bad] tak,
  aby obsahoval aj možnosť chyby. Tento typ nazveme natoption.
*)

Inductive natoption : Type := 
| None
| Some (n:nat)
.


(**
  Poznámka: 
  Konštruktory None a Some sú napísané
  s veľkým začiatočným písmenom podľa konvencie
  štandardnej knižnice Rocq.
  
  Vo všeobecnosti môžu názvy konštruktorov (a premenných)
  začínať veľkým alebo malým písmenom.
*)

(**
  Teraz je možné zmeniť pôvodnú definíciu funkcie nth_bad tak,
  aby vrátila None, keď je zoznam príliš krátky,
  a Some m, keď má zoznam dostatok prvkov a m
  sa nachádza na pozícii n.

  Túto novú funkciu nazveme nth_error,
  aby sme naznačili, že môže skončiť chybou.
*)

Fixpoint nth_error (l:natlist) (n:nat) : natoption := 
match l with
| []     => None
| hd::tl => match n with
           | 0 => Some hd
           | S m => nth_error tl m end
end.

Compute nth_error [] 4.
Compute nth_error [10;12;0] 1.
Compute nth_error [10;12;0] 2.


(** Option s chybovou hlaškou *)

Inductive natoptionerror : Type := 
| None' (s:string)
| Some' (n:nat)
.

Fixpoint nth_error' (l:natlist) (n:nat) : natoptionerror := 
match l with
| []     => None' "mimo rozsahu zoznamu"
| hd::tl => match n with
           | 0 => Some' hd
           | S m => nth_error' tl m end
end.

Compute nth_error' [] 4.
Compute nth_error' [10;12;0] 1.
Compute nth_error' [10;12;0] 2.


End natlist.


(*===========================================*)
(**   Polymorfné verzie list, pair, option  **)

(** V predchádzajúcej časti sme definovali typ dvojica,
zoznam a option pre prirodzené čísla. 
Avšak ak by sme potrebovali dané údajové štruktúry 
pre iný typ, bolo by potrebné všetky definície 
typov aj príslušných funkcií prepísať nanovo.

Ako už bolo uvedené na predchádzajúcich prednáškach, 
Rocq podporuje polymorfizmus a využijeme túto vlastnosť
na definíciu polymorfných typov dvojica, zoznam a option.
*)

(*===========================================*)
(*           Polymorfná verzia list          *)


Inductive list (X:Type) : Type :=
| nil 
| cons (x : X) (l: list X).

(**
  Čo vlastne je list?

  Dobrý spôsob, ako o tom uvažovať, je, že definícia list
  je funkcia z typov do induktívnych definícií; 
  alebo stručnejšie, list je funkcia z typov do typov. 

  Pre ľubovoľný konkrétny typ X je typ list X 
  induktívne definovaná množina zoznamov, 
  ktorých prvky sú typu X.
*)

(* Kontrola typu list *)
Check list.          (* list : Type -> Type *)

(**
  Parameter X v definícii list sa automaticky stáva parametrom 
  konštruktorov nil a cons — teda nil a cons sú teraz 
  polymorfné konštruktory.  

  Keď ich používame, musíme im ako prvý argument 
  poskytnúť typ prvkov zoznamu, ktorý konštruujeme.
*)

(* Polymorfné konštruktory *)
Check nil.       (* forall X : Type, list X *)
Check cons.      (* forall X : Type, X -> list X -> list X *)

(* Príklady *)
Check nil nat.        
(* prázdny zoznam typu nat *)

Check cons nat 1 (cons nat 2 (nil nat)).  
(**
  Povinnosť zadávať typový argument pri každom použití 
  konštruktora zoznamu je dosť zaťažujúca;
  čoskoro uvidíme spôsoby, ako túto potrebu anotácie znížiť.
*)

(** Definujme polymorfnú funkciu repeat *)
Fixpoint repeat (X:Type) (a:X) (count : nat): list X :=
match count with
| 0 => nil X
| S m => cons X a (repeat X a m) 
end.

Compute repeat bool true 5.

Compute repeat nat 1 5.

(** Odvodenie typovej anotácie *)
(* Definujme funkcie repeat bez explicitnej typovej anotácie *)

Fixpoint repeat' X a count: list X :=
match count with
| 0 => nil X
| S m => cons X a (repeat' X a m) 
end.

Check repeat'.

(* Automatické odvodzovanie implicitných typových argumentov *)
Fixpoint repeat'' X a count: list X :=
match count with
| 0 => nil _
| S m => cons _ a (repeat'' _ a m) 
end.

Check repeat''.

Definition list123' :=
  cons _ 1 (cons _ 2 (cons _ 3 (nil _))).
Check list123'.

(** Implicitné argumenty

  Je možné vyhnúť sa písaniu _ vo väčšine prípadov tak, 
  že Rocq vždy odvodí typový argument danej funkcie.

  Príkaz Arguments špecifikuje názov funkcie (alebo konštruktora)
  a potom zoznam argumentov, ktoré sa majú považovať za implicitné,
  každý uzavretý do zložených zátvoriek.
*)

(* Nastavenie implicitných argumentov pre konštruktory zoznamu *)
Arguments nil {X}.
Arguments cons {X}.
Arguments repeat {X}.

(**
  Teraz nemusíme poskytovať žiadne typové argumenty vôbec:
*)

Definition list123'' := cons 1 (cons 2 (cons 3 nil)).

(**
  Alternatívne môžeme deklarovať argument ako implicitný
  priamo pri definícii funkcie, 
  tým že ho uzavrieme do zložených zátvoriek 
  namiesto zátvoriek obyčajných.
*)

Fixpoint repeat''' {X : Type} (x : X) (count : nat) : list X :=
  match count with
  | 0 => nil
  | S count' => cons x (repeat''' x count')
  end.

(**
  Poznámka: ani pri rekurzívnom volaní funkcie repeat'''
  nemusíme poskytovať typový argument. 
  V skutočnosti by bolo nesprávne ho uviesť,
  pretože Rocq ho neočakáva.

  Tento štýl budeme používať vždy, keď je to možné, ale
  naďalej budeme používať explicitné deklarácie Arguments pre
  konštruktory induktívnych typov.  

  Dôvod je, že označenie parametra induktívneho typu ako implicitného
  spôsobí, že sa stane implicitným pre samotný typ, 
  nielen pre jeho konštruktory.
*)
(* Pri takomto prístupe vzniká jeden menší problém. 
   Rocq niekedy nemá dostatok informácii na odvodenie typu *)

Fail Definition mynil := nil nat.

Definition mynil : list nat := nil.
Definition mynil' := @nil nat.


(** Definícia polymorfnej funkcie pre spajanie zoznamov *)

Fixpoint append {X:Type} (l1 l2: list X) : list X := 
match l1 with
| nil => l2 
| cons x xs => cons x (append xs l2)
end.

Compute append (cons 2 nil) (cons 1 nil).

(**
  Napríklad, alternatívna definícia typu zoznamu:

  Inductive list' {X:Type} : Type :=
    | nil'
    | cons' (x : X) (l : list').

  Pretože X je deklarované ako implicitné 
  pre celú induktívnu definíciu vrátane list',
  teraz je nutné písať len list', 
  či už hovoríme o zoznamoch čísel, pravdivostných hodnôt
  alebo čomkoľvek inom, namiesto list' nat alebo list' bool. 
*)


(** Zavedenie štandardnej notácie pre zoznamy*)

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (append x y)
                     (at level 60, right associativity).

Check [1].
Compute [1;2]++[3;5;6].

(*===========================================*)
(*           Polymorfná verzia pair          *)

Inductive product (X:Type) (Y:Type): Type :=
| pair (m:X) (n:Y).

Check pair nat bool 3 true.
Check pair _ _ 3 true.

(* Nastavenie implicitných argumentov *)
Arguments pair {X} {Y}.

Check pair 3 true.

(* Zavedieme štandardnú notáciu pre dvojicu *)
Notation "( x , y )" := (pair x y).

(* Zavedieme štandardnú notáciu pre typ dvojica *)
Notation "X * Y" := (product X Y) : type_scope.

Check product. 
Check pair 3. 
Check pair 3 true. 
(* (3, true) : product  *)

Definition fst {X Y: Type} (p: X * Y): X := 
match p with
| (x, y) => x
end.

Check fst.


Definition snd {X Y: Type} (p: X * Y): Y := 
match p with
| (x, y) => y
end.

Check snd.

Compute (fst (1,true)).
Compute (snd (1,true)).
Compute (fst ((false,5),true)).
Compute (fst (1,true)).

Definition swap {X Y : Type} (p: X * Y): Y * X :=
match p with 
| (x,y) => (y,x)
end. 

Theorem swap_swap_p:
  forall {X Y: Type} (p: X*Y), p = swap (swap p).
Proof.
intros.
destruct p.
simpl.
reflexivity.
Qed.


(*===========================================*)
(*         Polymorfná verzia option          *)
(**
  Posledným polymorfný typ v rámci tejto prednášky 
  bude polymorfný option, ktorý zovšeobecňuje natoption 
  z predchádzajúcej časti. 

  (Definíciu umiestňujeme do modulu, pretože štandardná 
  knižnica už definuje option a práve túto použijeme 
  nižšie pri redefinícii funkcie nth_error.)
*)

Module PolymorphicOption.

  (* Polymorfná definícia option *)
  Inductive option (X: Type) : Type :=
    | Some (x : X)
    | None.

  (* Nastavenie implicitného argumentu *)
  Arguments Some {X}.
  Arguments None {X}.

End PolymorphicOption.

(* Polymorfná verzia funkcie nth_error *)

Fixpoint nth_error {X:Type} (l:list X) (n:nat): option X := 
match l with
| []     => None
| hd::tl => match n with
           | 0    => Some hd
           | S m  => nth_error tl m end
end.

Compute nth_error [] 4.
Compute nth_error [10;12;0] 1.
Compute nth_error [10;12;0] 2.

