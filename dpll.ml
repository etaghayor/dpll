open List

(* fonctions utilitaires *********************************************)
(* filter_map : ('a -> 'b option) -> 'a list -> 'b list
   disponible depuis la version 4.08.0 de OCaml dans le module List :
   pour chaque élément de `list', appliquer `filter' :
   - si le résultat est `Some e', ajouter `e' au résultat ;
   - si le résultat est `None', ne rien ajouter au résultat.
     Attention, cette implémentation inverse l'ordre de la liste *)
let filter_map filter list =
  let rec aux list ret =
    match list with
    | []   -> ret
    | h::t -> match (filter h) with
      | None   -> aux t ret
      | Some e -> aux t (e::ret)
  in aux list []

(* print_modele : int list option -> unit
   affichage du résultat *)
let print_modele: int list option -> unit = function
  | None   -> print_string "UNSAT\n"
  | Some modele -> print_string "SAT\n";
    let modele2 = sort (fun i j -> (abs i) - (abs j)) modele in
    List.iter (fun i -> print_int i; print_string " ") modele2;
    print_string "0\n"


(* pretty prints *)


let pretty_print_clause c = 
  let rec aux res = function
    | [] -> res
    | [x] -> res^(string_of_int x)
    | x::xs -> aux ((string_of_int x) ^", " ^ res) xs 
  in  aux "" c;;

let pretty_print_clauses l =
  let rec aux res = function
    | [] -> res
    | [x] -> res^"["^(pretty_print_clause x)^"]\n"
    | x::xs -> aux ("["^(pretty_print_clause x)^"];"^res) xs 
  in print_string(aux "" l);;

let pretty_print_unit =function
  | None -> print_string "no unit clause found\n"
  | Some x -> Printf.printf "%d\n" x;;

let pretty_print_pur =function
  | None -> print_string "no pur clause found\n"
  | Some x -> Printf.printf "%d\n" x;;


(* ensembles de clauses de test *)
let exemple_3_12 = [[1;2;-3];[2;3];[-1;-2;3];[-1;-3];[1;-2]]
let exemple_7_2 = [[1;-1;-3];[-2;3];[-2]]
let exemple_7_4 = [[1;2;3];[-1;2;3];[3];[1;-2;-3];[-1;-2;-3];[-3]]
let exemple_7_8 = [[1;-2;3];[1;-3];[2;3];[1;-2]]
let systeme = [[-1;2];[1;-2];[1;-3];[1;2;3];[-1;-2]]
let coloriage = [[1;2;3];[4;5;6];[7;8;9];[10;11;12];[13;14;15];[16;17;18];[19;20;21];[-1;-2];[-1;-3];[-2;-3];[-4;-5];[-4;-6];[-5;-6];[-7;-8];[-7;-9];[-8;-9];[-10;-11];[-10;-12];[-11;-12];[-13;-14];[-13;-15];[-14;-15];[-16;-17];[-16;-18];[-17;-18];[-19;-20];[-19;-21];[-20;-21];[-1;-4];[-2;-5];[-3;-6];[-1;-7];[-2;-8];[-3;-9];[-4;-7];[-5;-8];[-6;-9];[-4;-10];[-5;-11];[-6;-12];[-7;-10];[-8;-11];[-9;-12];[-7;-13];[-8;-14];[-9;-15];[-7;-16];[-8;-17];[-9;-18];[-10;-13];[-11;-14];[-12;-15];[-13;-16];[-14;-17];[-15;-18]]

(********************************************************************)


(*simplifie*)
(*Si la valeur i apparait dans la liste, on peut la supprimer, sinon, on garde seulement les valaurs non égales à -i *)

(* simplifie : int -> int list list -> int list list 
   applique la simplification de l'ensemble des clauses en mettant
   le littéral i à vrai *)


let simplifie i =
  filter_map (fun x -> if mem i x then None else
                 Some (filter(fun l -> l != (-i)) x))

(*unitaire*)
(* unitaire : int list list -> int
   - si `clauses' contient au moins une clause unitaire, retourne
      le littéral de cette clause unitaire ;
   - sinon, lève une exception `Not_found' *)
let rec unitaire clauses =
  match clauses with
  | [] -> None
  | [x]::xs -> Some x
  | x::xs -> unitaire xs;;


(*pur*)

let rec add_var res_pos res_neg  =function
  | [] -> res_pos,res_neg
  | hd::tl -> if hd>0 then add_var (hd::res_pos) res_neg tl else
      add_var res_pos (hd::res_neg) tl

let rec list_of_var_opt clauses =
  let rec aux res_pos res_neg = function
    | [] -> List.sort_uniq (-) res_pos, List.sort_uniq (fun x -> fun y -> y-x) res_neg
    | l::ls -> let pos, neg = add_var res_pos res_neg l in
      aux pos neg ls in aux [] [] clauses

let rec find_pur p n =  match p,n with
    | [], [] -> None
    | [], y::ys -> Some y
    | x::xs, [] -> Some x
    | x::xs, y::ys -> if abs x < (abs y) then Some x else
      if abs x > (abs y) then Some y else find_pur xs ys 

(* pur : int list list -> int
   - si `clauses' contient au moins un littéral pur, retourne
      ce littéral ;
   - sinon, lève une exception `Failure "pas de littéral pur"' *)
(* let rec pur clauses = let var_list = list_of_var clauses in
   match (List.find (fun x -> (not (List.mem (-x) var_list))) var_list) with
   | x -> Some x
   | exception Not_found -> None;; *)

let rec pur clauses = let pos,neg = list_of_var_opt clauses in find_pur pos neg

(* solveur_split : int list list -> int list -> int list option
   exemple d'utilisation de `simplifie' *)
(* cette fonction ne doit pas être modifiée, sauf si vous changez 
   le type de la fonction simplifie *)
let rec solveur_split clauses interpretation =
  (* l'ensemble vide de clauses est satisfiable *)
  if clauses = [] then Some interpretation else
    (* un clause vide est insatisfiable *)
  if mem [] clauses then None else
    (* branchement *) 
    let l = hd (hd clauses) in
    let branche = solveur_split (simplifie l clauses) (l::interpretation) in
    match branche with
    | None -> solveur_split (simplifie (-l) clauses) ((-l)::interpretation)
    | _    -> branche

(* tests *)
(* let () = print_modele (solveur_split systeme []) *)
(* let () = print_modele (solveur_split coloriage []) *)

(* solveur dpll récursif *)

(* solveur_dpll_rec : int list list -> int list -> int list option *)
let rec solveur_dpll_rec clauses interpretation =
  if clauses = [] then Some interpretation else
  if mem [] clauses then None else
    match unitaire clauses with
    | Some u -> solveur_dpll_rec (simplifie u clauses) (u::interpretation)
    | None -> match pur clauses with
      | Some p -> solveur_dpll_rec (simplifie p clauses) (p::interpretation)
      | None -> 
        let l = hd (hd clauses) in
        let branche = solveur_dpll_rec (simplifie l clauses) (l::interpretation) in
        match branche with
        | None -> solveur_dpll_rec (simplifie (-l) clauses) ((-l)::interpretation)
        | _    -> branche


(* tests *)
(* let () = print_modele (solveur_dpll_rec systeme []) *)
(* let () = print_modele (solveur_dpll_rec coloriage []) *)

let () =
  let clauses = Dimacs.parse Sys.argv.(1) in
  (* let pos,neg = list_of_var_opt clauses in *)
  (* List.iter(Printf.printf "%d ") (List.sort_uniq (-) pos); *)
  (* List.iter(Printf.printf "%d ") (List.sort_uniq (fun x -> fun y -> y-x) neg); *)
  (*List.iter(Printf.printf "%d " ) pos;
    List.iter(Printf.printf "%d " ) neg; *)
  print_modele (solveur_dpll_rec clauses []);;
