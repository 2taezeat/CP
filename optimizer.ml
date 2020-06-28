open T

let cp_check = ref false
let cf_check = ref false
let de_check = ref false

let rec copy_propagation : T.program -> T.program
= fun pgm0 -> match pgm0 with
	| hd :: tl -> (let () = cp_check := false in
          match hd with 
		| ( label0, COPY(var1, var2) ) -> hd::( copy_propagation (help_c_p tl !cp_check var1 var2) )
		| _ -> hd::( copy_propagation tl )
         )
    | [] -> []

and help_c_p : T.program -> bool -> string -> string -> T.program
= fun pgm0 bool0 x y -> match pgm0 with
	| hd::tl -> ( if (!cp_check = true) then (hd::tl) else
		match hd with
		| ( label0, ASSIGNV (var1, bop, var2, var3) ) -> if (x = var1) then let () = cp_check := true in hd::tl
			else if (x = var2 && x = var3) then
				let label_instrlist1 = ( label0, ASSIGNV (var1, bop, y, y) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else if (x = var2) then 
				let label_instrlist1 = ( label0, ASSIGNV (var1, bop, y, var3) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else if (x = var3) then 
				let label_instrlist1 = ( label0, ASSIGNV (var1, bop, var2, y) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, ASSIGNC (var1, bop, var2, num0) ) -> if (x = var1) then let () = cp_check := true in hd::tl
			else if (x = var2) then 
				let label_instrlist1 = ( label0, ASSIGNC (var1, bop, y, num0) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, ASSIGNU (var1, uop, var2) ) -> if (x = var1) then let () = cp_check := true in hd::tl
			else if (x = var2) then 
				let label_instrlist1 = ( label0, ASSIGNU (var1, uop, y) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, COPY (var1, var2) ) ->  if (x = var1) then let () = cp_check := true in hd::tl
			else if (x = var2) then  
				let label_instrlist1 = ( label0, COPY (var1, y) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, COPYC (var1, num0) ) -> if (x = var1) then let () = cp_check := true in hd::tl
			else hd::(help_c_p tl false x y)

		| ( label0, CJUMP (var1, label1) ) -> if (x = var1) then 
				let label_instrlist1 = ( label0, CJUMP (y, label1) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, CJUMPF (var1, label1) ) -> if (x = var1) then 
				let label_instrlist1 = ( label0, CJUMPF (y, label1) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, STORE (array1, var1) ) -> if (x = var1) then 
				let label_instrlist1 = ( label0, STORE (array1, y) )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, READ var1 ) -> if (x = var1) then 
				let label_instrlist1 = ( label0, READ y )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| ( label0, WRITE var1 ) -> if (x = var1) then 
				let label_instrlist1 = ( label0, WRITE y )::tl in
				let label_instrlist2 = (help_c_p label_instrlist1 false x y) in label_instrlist2
			else hd::(help_c_p tl false x y)

		| _ -> hd::(help_c_p tl false x y)
	)
    | [] -> []

let rec constant_fold : T.program -> T.program
= fun pgm0 -> match pgm0 with
	| hd::tl -> ( let () = cf_check := false in
		match hd with
		| ( label0 ,COPYC(var0, num0) ) -> hd::( constant_fold (help_c_f tl !cf_check var0 num0) )
		| _ -> hd::(constant_fold tl)
    )
    | [] -> []
	
and help_c_f : T.program -> bool -> string -> int -> T.program
= fun pgm0 bool0 x num0 -> match pgm0 with
	| hd::tl -> ( if (!cf_check = true) then (hd::tl) else
		match hd with
		| ( label0, ASSIGNV (var1, bop, var2, var3) ) -> if (x = var1) then let () = cf_check := true in hd::tl
			else if (x = var2 && x = var3) then
				let label_instrlist1 = ( label0, COPYC (var1, (binary_eval num0 bop num0)) )::tl in
				let label_instrlist2 = (help_c_f label_instrlist1 false x num0) in label_instrlist2
			else if (x = var3) then 
				let label_instrlist1 = ( label0, ASSIGNC (var1, bop, var2, num0) )::tl in
				let label_instrlist2 = (help_c_f label_instrlist1 false x num0) in label_instrlist2
			else hd::(help_c_f tl false x num0)

		| ( label0, ASSIGNC (var1, bop, var2, num0) ) -> if (x = var1) then let () = cf_check := true in hd::tl
			else if (x = var2) then
				let label_instrlist1 = ( label0, COPYC (var1, (binary_eval num0 bop num0)) )::tl in
				let label_instrlist2 = (help_c_f label_instrlist1 false x num0) in label_instrlist2
			else hd::(help_c_f tl false x num0)

		| ( label0, ASSIGNU (var1, uop, var2) ) -> if (x = var1) then let () = cf_check := true in hd::tl
			else if (x = var2) then
				let label_instrlist1 = ( label0, COPYC (var1, unary_eval uop num0) )::tl in
				let label_instrlist2 = (help_c_f label_instrlist1 false x num0) in label_instrlist2
			else hd::(help_c_f tl false x num0)

		| ( label0, COPY (var1, var2) ) -> if (x = var1) then let () = cf_check := true in hd::tl
			else if (x = var2) then
				let label_instrlist1 = ( label0, COPYC (var1, num0) )::tl in
				let label_instrlist2 = (help_c_f label_instrlist1 false x num0) in label_instrlist2
			else hd::(help_c_f tl false x num0)

		| ( label0, COPYC (var1, num0) ) -> if (x = var1) then let () = cf_check := true in hd::tl
			else hd::(help_c_f tl false x num0)

		| _ -> hd::(help_c_f tl false x num0)
	)
    | [] -> []


and binary_eval : int -> T.bop -> int -> int
= fun num1 bop num2 -> match bop with
	| T.ADD -> num1 + num2
	| T.SUB -> num1 - num2
	| T.MUL -> num1 * num2
	| T.DIV -> num1 / num2

	| T.LT -> if num1 < num2 then 1 else 0
	| T.LE -> if num1 <= num2 then 1 else 0
	| T.GT -> if num1 > num2 then 1 else 0
	| T.GE -> if num1 >= num2 then 1 else 0
	| T.EQ -> if num1 = num2 then 1 else 0

	| T.AND -> if ((num1 != 0) && (num2 != 0)) then 1 else 0
	| T.OR -> if ((num1 != 0) || (num2 != 0)) then 1 else  0


and unary_eval : T.uop -> int -> int
= fun uop num1 -> match uop with
	| T.MINUS -> (-num1)
	| T.NOT -> if num1 = 0 then 1 else 0


let rec deadcode_elimin : T.program -> string list ref -> T.program
= fun pgm0 var_rlist-> match pgm0 with
	| hd::tl -> ( let () = de_check := false in
	match hd with
	| ( label0, COPY (var1, var2) ) -> 
	if (List.mem var1 !var_rlist = false) then (
		if (help_d_e tl !de_check var1 = true) then (
			if (label0 = 0) then deadcode_elimin tl var_rlist else deadcode_elimin ( (label0, snd (List.hd tl) )::(List.tl tl) ) var_rlist ) 
		else let () = var_rlist := ( !var_rlist @ [var1] ) in hd::( deadcode_elimin tl var_rlist )
	) else hd::(deadcode_elimin tl var_rlist)

	| ( label0, COPYC (var1, num0) ) -> 
	if (List.mem var1 !var_rlist = false) then (
		if (help_d_e tl !de_check var1 = true) then (
			if (label0 = 0) then deadcode_elimin tl var_rlist else deadcode_elimin ( (label0, snd (List.hd tl) )::(List.tl tl) ) var_rlist )
		else let () = var_rlist := ( !var_rlist @ [var1] ) in hd::( deadcode_elimin tl var_rlist )
	) else hd::(deadcode_elimin tl var_rlist)

	| _ -> hd::(deadcode_elimin tl var_rlist)
	)
	| [] -> []


and help_d_e : T.program -> bool -> string -> bool
= fun pgm0 bool0 x ->  match pgm0 with
	| hd::tl -> ( if (!de_check = true) then false else 
		match hd with
		| ( label0, ASSIGNV (var1, bop, var2, var3) ) ->  if (x = var1) then let () = de_check := true in true 
			else if (x = var2) then false else if (x = var3) then false else (help_d_e tl false x)

		| ( label0, ASSIGNC (var1, bop, var2, num0) ) -> if (x = var1) then let () = de_check := true in true
			else if (x = var2) then false else (help_d_e tl false x)

		| ( label0, ASSIGNU (var1, uop, var2) ) -> if (x = var1) then let () = de_check := true in true
			else if (x = var2) then false else (help_d_e tl false x)

		| ( label0, COPY (var1, var2) ) -> if (x = var1) then let () = de_check := true in true
			else if (x = var2) then false else (help_d_e tl false x)

		| ( label0, COPYC (var1, num0) ) -> if (x = var1) then let () = de_check := true in true else (help_d_e tl false x)

		| ( label0, CJUMP (var1, label1) ) -> if (x = var1) then false else (help_d_e tl false x)

		| ( label0, CJUMPF (var1, label1) ) -> if (x = var1) then false else (help_d_e tl false x)  
   
		| ( label0, LOAD (var1, (array1, array2)) ) -> if (x = var1) then false else if (x = array1) then false
			else if (x = array2) then false else (help_d_e tl false x)

		| ( label0, STORE ((array1, array2), var1) ) -> if (x = var1) then false else if (x = array1) then false
			else if (x = array2) then false else (help_d_e tl false x)

		| ( label0, READ var1 ) -> if (x = var1) then false else (help_d_e tl false x)

		| (label0, WRITE var1 ) ->if (x = var1) then false else (help_d_e tl false x)

		| _ -> (help_d_e tl false x)
		)
	| [] -> true	
	
let rec opti_basicblock : T.program  -> ( T.program ) list
= fun labinstrlist -> let blockref_list = ref [ List.hd labinstrlist ] in
					let blocklist1 = leader_extr labinstrlist !blockref_list in 
					let int_list = leader_int blocklist1 labinstrlist in 
					let blocklist2 = block_division labinstrlist int_list in blocklist2


and leader_extr : T.program -> T.program -> T.program
= fun labinstrlist blocklist -> match labinstrlist with
	| h::t-> ( match h with
		| (0, instr) -> ( match instr with
			| CJUMP (var1,label1) -> let update_block_list = blocklist @ [ List.hd t ]
			 in leader_extr (List.tl t) update_block_list
			 
			| CJUMPF (var1, label1) -> let update_block_list = blocklist @ [ List.hd t ]
			 in leader_extr (List.tl t) update_block_list

			| UJUMP (label1) -> let update_block_list = blocklist @ [ List.hd t ] 
			 in leader_extr (List.tl t) update_block_list
			| _ -> leader_extr t blocklist )
		| (_, _) -> let update_block_list = blocklist @ [(h)] in leader_extr t update_block_list
	)
	| [] -> blocklist


and h1 : T.linstr list -> T.linstr -> int
= fun lst x -> if (List.hd lst = x) then 0 else (h1 (List.tl lst) x ) + 1

and leader_int : T.linstr list -> T.linstr list -> int list
= fun blocklist0 labinstrlist0 -> match blocklist0 with
| [] -> []
| hd::tl -> (h1 labinstrlist0 hd)::(leader_int tl labinstrlist0) 

and add_f1 : T.linstr list ref -> T.linstr -> unit
= fun reflist label0 -> let addl = ( reflist := !reflist @ [ label0 ] ) in addl

and add_f2 : T.linstr list list ref -> T.linstr list -> unit
= fun reflist block0 -> let addb = ( reflist := !reflist @ [ block0 ] ) in addb

and block_division : T.linstr list -> int list -> (T.linstr list) list
= fun labinstrlist intlist->
	let tlabel = ref [] in 
	let tblock = ref [] in
	let lengthintlist = List.length intlist in

	let add_label label = add_f1 tlabel label in
	let add_block block = add_f2 tblock block in 

	for i = 0 to lengthintlist -1 do
		let () = tlabel := [] in 
		if i = (lengthintlist - 1) then 
		( for j = List.nth intlist i to List.length labinstrlist -1 do
			add_label (List.nth labinstrlist j) done;
			add_block !tlabel )

		else ( for j = List.nth intlist i  to (List.nth intlist (i+1))-1 do
			 	add_label (List.nth labinstrlist j) done;
			 	add_block !tlabel ) done; !tblock
   

let rec opti_pgm : T.program  -> T.program 
= fun pgm0 -> let pgm1 = copy_propagation pgm0 in 
				let pgm2 = constant_fold pgm1 in pgm2
	
and opti_pgmlist : ( T.program ) list -> T.program 
= fun pgmlist -> match pgmlist with
	| hd::tl -> ( let op_pgm0 = opti_pgm hd in 
		        let op_pgmlist0 = opti_pgmlist tl in op_pgm0 @ op_pgmlist0 )
    | [] -> []
	
let rec skip_eraser : T.program -> T.program
=fun pgm0 -> match pgm0 with
	| hd :: next :: tl -> (
		match hd with
		| (label0, SKIP) -> let (label1, code1) = next in ( label0,code1 )::( skip_eraser tl )
		| _ -> hd :: ( skip_eraser (next::tl) )
		                    )
    | [] -> []
	| _ -> pgm0

let rec optimize : T.program -> T.program
= fun pgm0 -> let var_rlist = ref [] in let skiped_pgm = skip_eraser pgm0 in 
			let basicb_list = opti_basicblock skiped_pgm in let op_pgmlist0 = opti_pgmlist basicb_list in
	        let result_pgm = deadcode_elimin op_pgmlist0 var_rlist in result_pgm