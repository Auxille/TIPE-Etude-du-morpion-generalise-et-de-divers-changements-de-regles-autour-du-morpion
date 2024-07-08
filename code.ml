let () = Random.self_init()
type joueur = Vide | J1| J2 (*Type permetant de remplir la grille *)
type bool_partiel = V | F | I (*Cette implémentation des booléens permet d'indiqueur quand sa valeur logique est indeterminée *)
type lit = V_ of int | N of int (*Désigne les littéraux, N veut dire Négation*)
type clause = lit list (*Une clause va être une liste de littéraux *)
type formule = {f :clause list; nb_V : int; nb_cl: int;  cnf: bool} 
(*le booléen cnf infique si la formule est une dnf ou une cnf, nb_V correspond au nombre de variables, nb_cl au nombre de clauses, f est une liste de clauses*)
type morpion = {
  grille : joueur array array; (*La grille remplie du type joueur *)
  misere: bool; (*Implémentation de la variante misère *)
  mutable joueur : joueur; (*Garde une trace du joueur dont c'est le tour de jouer *)
  valu_j1: bool_partiel array; (*Valuation associée au joueur 1, mis à V si la case x*n + y de la grille vaut J1, F si elle vaut J2, I si elle est vide *)
  valu_j2: bool_partiel array; (*Celle associée au joueur 2, sur le même principe en inversant J1 et J2 *)
  phi: formule} (*Formule logique correspondant aux conditions de victoires de la règle du morpion actuelle*)


let rec parcours_clause_conjonctive (clause : clause) (valu: bool_partiel array): bool = match clause with
  |[]->false
  |V_ x ::t when valu.(x)=V-> true
  |N x :: t when valu.(x)=F->true
  |_::t ->parcours_clause_conjonctive
            t valu

let parcours_phi_cnf (phi: formule) (valu: bool_partiel array): int*bool  = 
  let rec aux f  acc= match f with
    |[]-> acc, (acc = phi.nb_cl)
    |cl::t-> 
        if parcours_clause_conjonctive
            cl valu then aux t (acc +1 )
        else aux t acc
  in
  aux phi.f 0
let rec parcours_clause_disjonctive (clause: clause) (valu: bool_partiel array) : bool = match clause with
  |[]->true
  |V_ x::t|N x::t when valu.(x)=I->false
  |V_ x::t when valu.(x)=F -> false
  |N x :: t when valu.(x)=V->false
  |_::t-> parcours_clause_disjonctive t valu

let parcours_phi_dnf (phi : formule) (valu: bool_partiel array): int* bool = 
  let rec aux f = match f with
    |[]->0, false
    |cl::t->
        if parcours_clause_disjonctive cl valu then 1, true
        else aux t 
  in aux phi.f 

let eval (phi : formule) (valu: bool_partiel array) : int*bool = match phi.cnf with
  |true -> parcours_phi_cnf phi valu
  |false -> parcours_phi_dnf phi valu


let morpion_init (n: int) (regle : int->formule) (mis: bool) : morpion= 
  let form = regle n in
  let g = Array.make_matrix n n Vide in
  let j1 = Array.make (n*n) I in
  let j2 = Array.make (n*n) I in
  {grille = g; 
   misere = mis; 
   joueur = J1; 
   valu_j1 = j1; 
   valu_j2 = j2 ;
   phi = form} 


let reset (m: morpion):unit = 
  let n= Array.length m.grille in
  for i=0 to n-1 do
    for j=0 to n-1 do
      m.grille.(i).(j) <- Vide;
      m.valu_j1.(i*n + j)<- I;
      m.valu_j2.(i*n + j)<- I
    done;
  done

let regle_basique (n: int): formule =
  let cnf = false in
  let nb_v = n*n in
  let nb_cl = (2*n +2) in
  let diag = ref [] in
  let anti_diag = ref [] in
  let phi = ref [] in
  for i=0 to n-1 do
    diag:= V_ (i*n + i):: !diag;
    anti_diag := V_ (i*n + n-i)::!diag;
    let col_i = ref [] in 
    let lig_i = ref [] in
    for j=0 to n-1 do
      lig_i:= V_ (i*n + j)::!lig_i;
      col_i:= V_ (i + j*n):: !col_i
    done;
    phi := (!col_i):: (!lig_i) :: !phi
  done;
  phi := (!diag) :: (!anti_diag) :: !phi;
  {f= !phi; nb_V = nb_v; nb_cl= nb_cl; cnf = cnf}

let sans_diag (n: int): formule =   
  let cnf = false in
  let nb_v = n*n in
  let nb_cl = (2*n ) in
  let phi = ref [] in
  for i=0 to n-1 do
    let col_i = ref [] in 
    let lig_i = ref [] in
    for j=0 to n-1 do
      lig_i:= V_ (i*n + j)::!lig_i;
      col_i:= V_ (i + j*n):: !col_i
    done;
    phi := (!col_i):: (!lig_i) :: !phi
  done;
  {f= !phi; nb_V = nb_v; nb_cl= nb_cl; cnf = cnf}

let modulo (n: int): formule =
  let cnf = false in
  let nb_v = n*n in
  let nb_cl = (4*n ) in
  let phi = ref [] in
  for i=0 to n-1 do
    let col_i = ref [] in 
    let lig_i = ref [] in
    let diag_i = ref [] in
    let anti_diag_i = ref [] in
    for j=0 to n-1 do
      lig_i:= V_ (i*n + j)::!lig_i;
      col_i:= V_ (i + j*n):: !col_i;
      diag_i:= V_ (j*n + (j+i mod n) ) ::!diag_i;
      anti_diag_i := V_ (j*n + (i-j mod n))::!anti_diag_i
    done;
    phi := (!anti_diag_i)::(!diag_i)::(!col_i):: (!lig_i) :: !phi
  done;
  {f= !phi; nb_V = nb_v; nb_cl= nb_cl; cnf= cnf}


let genere_cnf (cl: int) (k: int) (n: int): formule = (* Pour l'utilser en règle, on va curryfier le nombre de clauses et d'éléments par clauses *)
  let cnf = true in
  let nb_v = n*n in
  let phi = ref [] in
  let vu = Array.make nb_v false in
  for i=0 to cl-1 do
    let clau = ref [] in
    for j=0 to k-1 do
      let y = ref (Random.int nb_v) in
      while vu.(!y) do
        y := Random.int nb_v 
      done;
      vu.(!y)<-true;
      match Random.bool () with
      |false -> clau := N !y::!clau
      |true-> clau := V_ !y::!clau
    done;
    for j=0 to nb_v -1 do
      vu.(j)<-false
    done;
    phi:= (!clau)::!phi
  done;
  {f= !phi; nb_V = nb_v; nb_cl= cl;cnf = cnf}


let coups_possibles_tab (morpion: morpion): (int*int) array =
  let n = Array.length morpion.grille in
  let l = ref [] in
  for i = 0 to n-1 do
    for j=0 to n-1 do
      if morpion.grille.(i).(j) = Vide then l := (i, j):: !l
    done
  done;
  let p = List.length !l in
  let tab = Array.make p (0,0) in
  let rec aux l acc= match l with
    |[] -> ()
    |(i, j):: s -> tab.(acc) <- (i, j); aux s (acc+1)
  in 
  aux !l 0;
  tab


let coups_possibles_list (morpion: morpion): (int*int) list =
  let n = Array.length morpion.grille in
  let l = ref [] in
  for i = 0 to n-1 do
    for j=0 to n-1 do
      if morpion.grille.(i).(j) = Vide then l := (i, j):: !l
    done
  done;
  !l

let joueur_suivant (j: joueur): joueur = match j with
  |J1->J2
  |J2->J1
  |Vide-> failwith "impossible"

let annul_coup (x: int) (y: int) (m: morpion): unit = 
  let n = Array.length m.grille in
  m.joueur <- joueur_suivant m.joueur;
  m.grille.(x).(y) <- Vide;
  m.valu_j1.(x*n + y)<-I;
  m.valu_j2.(x*n+ y) <-I


let rec find (l: 'a list) (x: 'a): bool = match l with
  |[]-> false
  |s::t when s=x -> true
  |_::t -> find t x

let jouer_coup (x: int) (y: int) (m: morpion): unit =
  let n = Array.length m.grille in
  m.grille.(x).(y)<- m.joueur;
  if m.joueur = J1 then (m.valu_j2.(x*n+y)<-V;m.valu_j1.(x*n+y)<-F)
  else (m.valu_j1.(x*n+y)<-V;m.valu_j2.(x*n+y)<-F);
  m.joueur<-joueur_suivant m.joueur;;

let strat_alea (m : morpion): unit  = (*Joue un coup aléatoire *) 
  let coups = coups_possibles_tab m in 
  let p = Array.length coups in
  let nb = Random.int p in
  let (x, y) = coups.(nb) in
  jouer_coup x y m


let morpion (m: morpion) (strat_j1: morpion -> unit) (strat_j2: morpion ->unit): joueur  =
  reset m ;
  let n = Array.length m.grille in
  let rec aux (p: int) (n: int) sat_j1 sat_j2= match p with
    |p when p = n*n -> if m.phi.cnf then (if sat_j1>sat_j2 then J1
                                          else (if sat_j1 = sat_j2 then Vide
                                                else J2))
        else Vide
    |p -> if (m.joueur=J1) then (
        strat_j1 m;  
        let (valeur1, b1)= eval m.phi m.valu_j1  in
        let (valeur2,b2) = eval m.phi m.valu_j2 in
        if (b1 && b2) then Vide
        else if (b1 && m.misere) then J2
        else if (b1 && not(m.misere)) then J1
        else (m.joueur <- joueur_suivant m.joueur; aux (p+1) n valeur1 sat_j2 )
      )
        else(
          strat_j2 m;
          let (valeur1, b1)= eval m.phi m.valu_j1  in
          let (valeur2,b2) = eval m.phi m.valu_j2 in
          if (b1 && b2) then Vide
          else if (b2 && m.misere) then J1
          else if (b2 && not(m.misere)) then J2
          else (m.joueur <- joueur_suivant m.joueur; aux (p+1) n valeur2 sat_j2 )
        ) 
  in aux 0 n 0 0;;


let print_grille (m: morpion): unit =
  let n = Array.length m.grille in
  for i=0 to n-1 do
    for j=0 to n-1 do
      match m.grille.(i).(j) with
      |Vide-> print_string "   |"
      |J1-> print_string " X |"
      |J2-> print_string " O |"
    done;
    print_newline();
  done;;
    
let est_plein (m:morpion)=
  coups_possibles_list m = []

let heuris_cnf (m: morpion): int* (int*int) =
  let tab= coups_possibles_tab m in
  let n = Array.length (m.grille) in 
  let p = Array.length tab in
  let max = ref 0 in
  if m.joueur = J1 then max := min_int
  else max := max_int;
  let coup = ref (0,0) in
  for i = 0 to p-1 do
    let (x, y) = tab.(i) in
    match m.joueur with
    |J1-> 
        m.valu_j1.(x*n + y)<-V;
        m.valu_j2.(x*n+ y)<-F;
        let j, b = eval m.phi m.valu_j1 in
        if b then (max := max_int; coup:= (x, y))
        else(
          let z, b = eval m.phi m.valu_j2 in
          if b then ()
          else (
            if !max < j-z then (max:=j-z; coup:= (x,y) )
          )
        );
        m.valu_j1.(x*n + y)<-I;
        m.valu_j2.(x*n+ y)<-I
    |J2->
        m.valu_j2.(x*n + y)<-V;
        m.valu_j1.(x*n+ y)<-F;
        let j, b = eval m.phi m.valu_j2  in
        if b then (max := min_int; coup:= (x, y))
        else(
          let z, b = eval m.phi m.valu_j1  in
          if b then ()
          else (
            if !max > z-j then (max:=z-j; coup:= (x,y) )
          )
        );
        m.valu_j1.(x*n + y)<-I;
        m.valu_j2.(x*n+ y)<-I
    |_-> failwith "impossible"
  done;
  !max, !coup 

let heuris_cnf_misere (m: morpion): int* (int*int) =
  let tab= coups_possibles_tab m in
  let n = Array.length (m.grille) in 
  let p = Array.length tab in
  let max = ref 0 in
  if m.joueur = J1 then max := min_int
  else max := max_int;
  let coup = ref (0,0) in
  for i = 0 to p-1 do
    let (x, y) = tab.(i) in
    match m.joueur with
    |J1-> 
        m.valu_j1.(x*n + y)<-V;
        m.valu_j2.(x*n+ y)<-F;
        let j, b = eval m.phi m.valu_j2 in
        if b then (max := max_int; coup:= (x, y))
        else(
          let z, b = eval m.phi m.valu_j2 in
          if b then ()
          else (
            if !max < -j+z then (max:=-j+z; coup:= (x,y) )
          )
        );
        m.valu_j1.(x*n + y)<-I;
        m.valu_j2.(x*n+ y)<-I
    |J2->
        m.valu_j2.(x*n + y)<-V;
        m.valu_j1.(x*n+ y)<-F;
        let j, b = eval m.phi m.valu_j1  in
        if b then (max := min_int; coup:= (x, y))
        else(
          let z, b = eval m.phi m.valu_j1  in
          if b then ()
          else (
            if !max > -z+j then (max:=-z+j; coup:= (x,y) )
          )
        );
        m.valu_j1.(x*n + y)<-I;
        m.valu_j2.(x*n+ y)<-I
    |_-> failwith "impossible"
  done;
  !max, !coup 

let minmax (h: morpion-> int* (int*int)) (p: int) (m: morpion): unit =(*On va curryfier l'heuristique et la profondeur pour l'utiliser en statégie *)
  assert (p>=1); 
  let rec aux prof coup_prec = 
    let (nb1, b1) = eval m.phi m.valu_j1 in
    let (nb2, b2) = eval m.phi m.valu_j2 in
    if (b1 && b2) then (0, coup_prec)
    else if b2 then (min_int, coup_prec)
    else if b1 then  (max_int, coup_prec)
    else if est_plein m then ((nb1 - nb2), (coup_prec))   
    else if prof = 1 then (h m)
    else(
      match m.joueur with
      |J1->
          let liste = coups_possibles_list m in
          let rec parcours_max l max coup= match l with
            |[] -> max , coup
            |(x2, y2):: t -> 
                jouer_coup x2 y2 m;
                let (ma, c) = aux (prof -1) (x2, y2) in
                annul_coup x2 y2 m;
                if ma> max then parcours_max l ma (x2,y2)
                else parcours_max l max coup
          in
          parcours_max liste 0 (0, 0)
      |J2->
          let liste = coups_possibles_list m in
          let rec parcours_min l min coup= match l with
            |[] -> min , coup
            |(x2, y2):: t -> 
                jouer_coup x2 y2 m;
                let (mi, c) = aux (prof -1) (x2, y2) in
                annul_coup x2 y2 m;
                if mi< min then parcours_min l mi (x2,y2)
                else parcours_min l min coup
          in
          parcours_min liste max_int (0, 0)
      |Vide->failwith "impossible")
  in 
  let valeur, (x, y) = aux p (-1, -1) in
  match (x,y) with
  |(x',y') when (x',y') = (-1, -1)->failwith "impossible car la partie est déjà finie dans ce cas"
  |(x',y')-> jouer_coup x y m

let minmax_blocage (h: morpion-> int* (int*int)) (p: int) (m: morpion): int* (int*int) =(*On va curryfier l'heuristique et la profondeur pour l'utiliser en statégie *)
  assert (p>=1); 
  let rec aux prof coup_prec = 
    let (nb1, b1) = eval m.phi m.valu_j1 in
    let (nb2, b2) = eval m.phi m.valu_j2 in
    if (b1 && b2) then (0, coup_prec)
    else if b2 then (min_int, coup_prec)
    else if b1 then  (max_int, coup_prec)
    else if est_plein m then ((nb1 - nb2), (coup_prec))   
    else if prof = 1 then (h m)
    else(
      match m.joueur with
      |J1->
          let liste = coups_possibles_list m in
          let rec parcours_max l max coup= match l with
            |[] -> max , coup
            |(x2, y2):: t -> 
                jouer_coup x2 y2 m;
                let (ma, c) = aux (prof -1) (x2, y2) in
                annul_coup x2 y2 m;
                if ma> max then parcours_max l ma (x2,y2)
                else parcours_max l max coup
          in
          parcours_max liste 0 (0, 0)
      |J2->
          let liste = coups_possibles_list m in
          let rec parcours_min l min coup= match l with
            |[] -> min , coup
            |(x2, y2):: t -> 
                jouer_coup x2 y2 m;
                let (mi, c) = aux (prof -1) (x2,y2) in
                annul_coup x2 y2 m;
                if mi< min then parcours_min l mi (x2,y2)
                else parcours_min l min coup
          in
          parcours_min liste max_int (0, 0)
      |Vide-> failwith "impossible")
  in 
  aux p (-1, -1) 

let score (x:int) (y: int) (m: morpion): int = 
  let n = Array.length m.grille in 
  let rec parcours_clause_gagnant cl= match cl with
    |[]->0
    |V_ (l) :: t -> (match m.joueur with
        |J1-> (match m.valu_j1.(l) with
            |F->0
            |V->1 + (parcours_clause_gagnant t)
            |I-> parcours_clause_gagnant t )
        |J2->
            (match m.valu_j2.(l) with
             |F->0
             |V-> (parcours_clause_gagnant t) -1
             |I-> parcours_clause_gagnant t)
        |Vide-> failwith "impossible")
    |N (l)::t -> failwith "impossible"
  in
  let rec parcours_clause_blocant cl= match cl with
    |[]->0
    |V_ (l) :: t -> (match m.joueur with
        |J1-> (match m.valu_j1.(l) with
            |F->1+ (parcours_clause_blocant t)
            |V->0
            |I-> parcours_clause_blocant t)
        |J2->(
            match m.valu_j2.(l) with
            |F->(parcours_clause_blocant t)  -1
            |V-> 0
            |I-> parcours_clause_blocant t)
        |Vide-> failwith "impossible")
    |N (l)::t -> failwith "impossible"
  in
  let rec aux phi acc = match phi with 
    |[]-> acc
    |cl::t ->match m.joueur with
      |J1-> if find cl (V_ (x*n+y))  then (let score_clause = (parcours_clause_gagnant cl) + (parcours_clause_blocant cl)  in aux t (acc + score_clause  +1))
          else aux t acc
      |J2->if find cl (V_ (x*n+y))  then (let score_clause = (parcours_clause_gagnant cl) + (parcours_clause_blocant cl)  in aux t (acc - score_clause  -1))
          else aux t acc
      |Vide-> failwith "impossible"
  in
  aux m.phi.f 0

let score_misere (x:int) (y: int) (m: morpion): int = 
  let n = Array.length m.grille in 
  let rec parcours_clause_blocant cl= match cl with
    |[]->0
    |V_ (l) :: t -> (match m.joueur with
        |J1-> (match m.valu_j1.(l) with
            |F->1+ (parcours_clause_blocant t)
            |V->0
            |I-> parcours_clause_blocant t)
        |J2->
            (match m.valu_j2.(l) with
             |F->(parcours_clause_blocant t)  -1
             |V-> 0
             |I-> parcours_clause_blocant t )
        |Vide -> failwith "impossible" )
    |_:: t-> failwith "impossible"
  in
  let rec aux phi acc = match phi with 
    |[]-> acc
    |cl::t ->match m.joueur with
      |J1-> if find cl (V_ (x*n+y))  then (let score_clause = -(parcours_clause_blocant cl)  in aux t (acc + score_clause  +1))
          else aux t acc
      |J2->if find cl (V_ (x*n+y))  then (let score_clause = (parcours_clause_blocant cl)  in aux t (acc + score_clause  -1))
          else aux t acc
      |Vide -> failwith "impossible" 
  in
  aux m.phi.f 0
let heuris_dnf (m: morpion): int* (int*int) = (*ici les dnf manipulées ne contiennent jamais de litteraux negatifs *)
  let coup_possibles = coups_possibles_list m in
  let rec aux l acc coup= match l with
    |[]->acc, coup
    |(x, y)::t -> match m.joueur with
      |J1-> jouer_coup x y m;
          let (_, b) = eval m.phi m.valu_j1 in
          annul_coup x y m;
          if b then max_int, (x,y)
          else(
            let nb = score x y m in 
            if nb>acc then aux l nb (x,y)
            else aux t acc coup
          )
      |J2 ->
          jouer_coup x y m;
          let (nb, b) = eval m.phi m.valu_j2 in
          annul_coup x y m;
          if b then min_int, (x,y)
          else(
            let nb = score x y m in 
            if nb<acc then aux l nb (x,y)
            else aux t acc coup
          )
      |Vide-> failwith "impossible"
  in
  aux coup_possibles 0 (0, 0)

let heuris_dnf_misere (m: morpion): int* (int*int) = (*ici les dnf manipulées ne contiennent jamais de litteraux negatifs *)
  let coup_possibles = coups_possibles_list m in
  let rec aux l acc coup= match l with
    |[]->acc, coup
    |(x, y)::t -> match m.joueur with
      |J1-> jouer_coup x y m;
          let (_, b) = eval m.phi m.valu_j2 in
          annul_coup x y m;
          if b then max_int, (x,y)
          else(
            let nb = score x y m in 
            if nb>acc then aux l nb (x,y)
            else aux t acc coup
          )
      |J2 ->
          jouer_coup x y m;
          let (nb, b) = eval m.phi m.valu_j1 in
          annul_coup x y m;
          if b then min_int, (x,y)
          else(
            let nb = score x y m in 
            if nb<acc then aux l nb (x,y)
            else aux t acc coup)
      |Vide-> failwith "impossible"
  in
  aux coup_possibles 0 (0, 0)
  
let strat_blocage (h: morpion -> int* (int*int))(p: int) (m:morpion) : unit = (*vole le coup optimal du 1er joueur*)
  m.joueur<- joueur_suivant m.joueur;
  let vale, (x,y) = minmax_blocage h p m in
  m.joueur<- joueur_suivant m.joueur;
  jouer_coup x y m
  
let heuris (m: morpion): int* (int*int) = 
  if m.phi.cnf then heuris_cnf m
  else heuris_dnf m

let heuris_cooperative (m:morpion): int* (int*int)=
  let tab= coups_possibles_tab m in
  let n = Array.length (m.grille) in 
  let p = Array.length tab in
  let max = ref 0 in
  if m.joueur = J1 then max := min_int
  else max := max_int;
  let coup = ref (0,0) in
  for i = 0 to p-1 do
    let (x, y) = tab.(i) in
    match m.joueur with
    |J1-> 
        m.valu_j1.(x*n + y)<-V;
        m.valu_j2.(x*n+ y)<-F;
        let j, b = eval m.phi m.valu_j1 in
        if b then (max := max_int; coup:= (x, y))
        else(
          if !max < j then (max:=j; coup:= (x,y) )
        )
        ;
        m.valu_j1.(x*n + y)<-I;
        m.valu_j2.(x*n+ y)<-I
    |J2->
        m.valu_j2.(x*n + y)<-V;
        m.valu_j1.(x*n+ y)<-F;
        let j, b = eval m.phi m.valu_j2  in
        if b then (max := min_int; coup:= (x, y))
        else(
          let z, b = eval m.phi m.valu_j1  in
          if b then ()
          else (
            if !max > -z+j then (max:=-z+j; coup:= (x,y) )
          )
        );
        m.valu_j1.(x*n + y)<-I;
        m.valu_j2.(x*n+ y)<-I
    |_-> failwith "impossible"
  done;
  !max, !coup 

let min_max_cooperatif (h:morpion-> int* (int*int)) (p: int) (m: morpion): unit =
  assert (p>=1); 
  let rec aux prof coup_prec = 
    let (nb, b) =(
      if m.joueur = J1 then eval m.phi m.valu_j1
      else eval m.phi m.valu_j2)
    in
    if b then match m.joueur with
      |J1 -> max_int, coup_prec
      |J2-> min_int, coup_prec
      |Vide-> failwith "impossible"
    else if prof = 1 then h m
    else(
      match m.joueur with
      |J1->
          let liste = coups_possibles_list m in
          let rec parcours_max l max coup= match l with
            |[] -> max , coup
            |(x2, y2):: t -> 
                jouer_coup x2 y2 m;
                let (ma, c) = aux (prof -1) (x2, y2) in
                annul_coup x2 y2 m;
                if -ma> max then parcours_max l (-ma) (x2,y2)
                else parcours_max l max coup
          in
          parcours_max liste min_int (0, 0)
      |J2->
          let liste = coups_possibles_list m in
          let rec parcours_min l min coup= match l with
            |[] -> min , coup
            |(x2, y2):: t -> 
                jouer_coup x2 y2 m;
                let (mi, c) = aux (prof -1) (x2,y2) in
                annul_coup x2 y2 m;
                if -mi< min then parcours_min l (-mi) (x2,y2)
                else parcours_min l min coup
          in
          parcours_min liste max_int (0, 0)
      |Vide->failwith "impossible"
    )
  in 
  let valeur, (x, y) = aux p (-1, -1) in
  match (x,y) with
  |(x',y') when (x',y') = (-1, -1)->failwith "impossible car la partie est déjà finie dans ce cas"
  |(x',y')-> jouer_coup x y m

let max_sat_valeur (phi: formule) :int =
  let valu = Array.make phi.nb_V I in
  let rec aux valu acc=
    if acc = phi.nb_V then (let (vale, b)= eval phi valu in vale)
    else (
      let bis = Array.copy valu in
      valu.(acc)<-V; bis.(acc)<-F;
      max (aux valu (acc+1)) (aux bis (acc+1))
    )
  in aux valu 0 

let morpion_max_sat m strat=
  let rec aux () =
    if est_plein m then (let (nb, v) = eval m.phi m.valu_j1 in nb)
    else (strat m; aux ())
  in aux ()
  
let string_of_joueur j = match j with
  |Vide -> "Vide"
  |J1-> "J1"
  |J2->"J2"

let n= 3;;
let k=1000;;
let cl= 4;;
let taille_cl = 3;;
let strat_j1 = strat_alea;;
let strat_j2 = strat_alea;;
let simulation_sans_diag =
  let m =morpion_init  n (sans_diag) false in
  let oc = open_out  "data_sans_diag.txt" in
  for i=0 to k-1 do
    Printf.fprintf oc "%s\n" (string_of_joueur (morpion m strat_j1 strat_j2))
  done;
  close_out oc
;;
let simulation_modulo =
  let m =morpion_init  n (modulo) false in
  let oc = open_out "data_modulo.txt" in 
  for i=0 to k-1 do
    Printf.fprintf oc "%s\n" (string_of_joueur (morpion m strat_j1 strat_j2))
  done;
  close_out oc
;;
let simulation_logique =
  let oc = open_out "data_logique.txt" in
  for i=0 to k-1 do
    let m =morpion_init  n (genere_cnf cl taille_cl) false in
    Printf.fprintf oc "%s\n" (string_of_joueur (morpion m strat_j1 strat_j2))
  done;
  close_out oc
;;
(*let check_win_1 m x y  =
let joeur = m.joueur +1 in 
let n = Array.length m.grille in
let c = ref true in
let l = ref true in
let a = ref true in
let d = ref true in
for i=0 to n-1 do
if m.grille.(x).(i) != joueur then l:= false;
if m.grille.(i).(y) != joueur then c:= false;
if m.grille.(i).(i)!= joueur then d:= false;
if m.grille.(i).(n-i-1) != joueur then a:= false
done;
if m.misere then (!a|| !d|| !l|| !c,true)
else (!a|| !d|| !l|| !c, false)
;;

let check_win_2 m x y  =
  let joeur = m.joueur +1 in
let n = Array.length m.grille in
let c = ref true in
let l = ref true in
let a = ref true in
let d = ref true in
for i=0 to n-1 do
  if m.grille.(x).(i) != joueur then l:= false;
  if m.grille.(i).(y) != joueur then c:= false;
  if m.grille.(x+i mod n).(y+i mod n)!= joueur then d:= false;
  if m.grille.(x-i mod n).(y+i mod n) != joueur then a:= false
done;
if m.misere then (!a|| !d|| !l|| !c,true)
else (!a|| !d|| !l|| !c, false)
;;

let check_win_3 m x y  =
  let n = Array.length m.grille in
  let c = ref true in
  let l = ref true in
  let joeur = m.joueur +1 in
  for i=0 to n-1 do
    if m.grille.(x).(i) != joueur then l:= false;
    if m.grille.(i).(y) != joueur then c:= false
  done;
  if m.misere then (!l|| !c,true)
  else (!l|| !c, false)
;; 
x'est les anciennes implémentations sans logique*)
    (*
let calcul_VA_non_mis n regle g  =
  let m = {grille =Array.make_matrix n n 0; misere= false; joueur= 0} in
  let va = ref [] in
  let rec simul m regle i = match i with
|n*n -> ()
|i when m.joueur = 0-> 
    let tab = coups_possibles tab in
    let j = Array.length tab in
    for k=0 to j-1 do
      let (x,y)= tab.(k) in
match regle m x y with
|(b,mi) when b && (not(mi))-> va:= 
|(b,_) when b -> ()
|(_,_)->
    joueur_coup x y m;
simul m regle (i+1);
annul_coup x y m
done;
|i ->
let tab = coups_possibles tab in
let j = Array.length tab in
for k=0 to j-1 do
  let (x,y)= tab.(k) in
  match regle m x y with
  |(_,_)->
      joueur_coup x y m;
      simul m regle (i+1);
      annul_coup x y m
done;
in simul m regle 0;
let v= List.length !va in
let tab= Array.make v 0 in
let rec parcours l acc= match l with
  |[]->()
  |s::t -> tab.(acc)<-s; parcours t (acc+1)
in
parcours va 0;
tab
let deg_sortant g =
  let n = Array.length g in
  let tab = Array.make n 0 in
  let rec parcours l acc = match l with
    |[]-> acc
    |_::t -> parcours t (acc+1)
  in
  for i=0 to n-1 do
    tab.(i)<-parcours g.(i) 0
  done;
  tab

let transpose g =
  let n = Array.length g in
  let g2 = Array.make n [] in
  let rec parcours_e l i= match l with
    |[]->()
    |s::t->g2.(s)<-i::g2.(s);parcours_e t i
  in
  for i=0 to n-1 do
    parcours_e g.(i) i
  done;
  g2


let calcul_VA_mis n regle g  =
  let m = {grille =Array.make_matrix n n 0; misere= true; joueur= 0} in
  let va = ref [] in
  let rec simul m regle i = match i with
    |n*n -> ()
    |i when m.joueur = 1-> 
        let tab = coups_possibles tab in
        let j = Array.length tab in
        for k=0 to j-1 do
          let (x,y)= tab.(k) in
          match regle m x y with
          |(b,mi) when b && (mi)-> va:= 
          |(b,_) when b -> ()
          |(_,_)->
              joueur_coup x y m;
              simul m regle (i+1);
              annul_coup x y m
        done;
    |i ->
        let tab = coups_possibles tab in
        let j = Array.length tab in
        for k=0 to j-1 do
          let (x,y)= tab.(k) in
          match regle m x y with
          |(_,_)->
              joueur_coup x y m;
              simul m regle (i+1);
              annul_coup x y m
        done;
  in simul m regle 0;
  let v= List.length !va in
let tab= Array.make v 0 in
let rec parcours l acc= match l with
  |[]->()
  |s::t -> tab.(acc)<-s; parcours t (acc+1)
in
parcours va 0;
tab

let attracteurs g mis n regle=
  let va = 
    if mis then calcul_VA_mis n regle g
    else calcul_VA_non_mis n regle g
  in
  let attract = ref [] in 
  let deg = deg_sortant g.graph in
  let trans = transpose g.graph in
  let rec parcours s =
    if not(find !a s) then(
      a:= s::!a in
  let rec aux l = match l with
    |[]->()
    |s2::t-> 
        deg.(s2)<- deg.(s2)-1;
        if (find s2 g.sa)|| (deg.(s2)=0) then parcours s2;
        aux t
  in
  aux trans.(s) 
)
else ()
in
let j= Array.length va in
for i=0 to j-1 do
  parcours va.(i)
done;
!attract
  Essai de calcul des attracteurs par un calcul du graphe de tous les coups possibles
  En calculant le nombre de sommets nécessaires pour obtenir le graphe théorique, je me suis
  rendu compte que pour n=3, une grille n*n génère quasiment 1 milion de sommets,
(la formule explicite est [la somme pour i=1 à n² des (n²)!/(n²-i!)]) 
  ce qui est beaucoup trop
  Donc je vais faire un min-max avec un potentiel élagage alpha-beta pour palier de profondeur infinie pour palier à ce problème.
                                                                                                                                   avec comme heuristique h(n) = score(n)
                                                                                                                                                                 *)
