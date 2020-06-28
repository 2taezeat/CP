
let rec plus_one : int ref -> int
=fun count -> count := !count + 1;
          !count

let tvar0 = ref 0
let label0 = ref 0


let rec translate_exp : S.exp -> T.var * T.linstr list
= fun exp0 -> match exp0 with
| S.ADD (exp1, exp2) -> 
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.ADD, t1, t2)) ] )
    
| S.SUB (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.SUB, t1, t2)) ] )

| S.MUL (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.MUL, t1, t2)) ] )
 
| S.DIV (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.DIV, t1, t2)) ] )
 
| S.MINUS (exp1) ->
    let (t1, code1) = translate_exp exp1 in
	let t2 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t2, code1 @ [ (T.dummy_label, T.ASSIGNU (t2, T.MINUS, t1)) ] )


| S.LT (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.LT, t1, t2)) ] )

| S.LE (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.LE, t1, t2)) ] )

| S.GT (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.GT, t1, t2)) ] )

| S.GE (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.GE, t1, t2)) ] )

| S.EQ (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.EQ, t1, t2)) ] )


| S.NOT (exp1) ->
    let (t1, code1) = translate_exp exp1 in
    let t2 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t2, code1 @ [ (T.dummy_label, T.ASSIGNU (t2, T.NOT, t1)) ] )

| S.OR (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.OR, t1, t2)) ] )

| S.AND (exp1, exp2) ->
    let (t1, code1) = translate_exp exp1 in
    let (t2, code2) = translate_exp exp2 in
    let t3 = ".t" ^ string_of_int (plus_one tvar0) in
    ( t3, code1 @ code2 @ [ (T.dummy_label, T.ASSIGNV (t3, T.AND, t1, t2)) ] )


| S.NUM (n1) -> let t1 = ".t" ^ string_of_int (plus_one tvar0) in
                ( t1, [ (T.dummy_label, T.COPYC (t1, n1)) ] )

| S.LV (lv1) -> ( match lv1 with
                | S.ID (id1) ->  let t1 = ".t" ^ string_of_int (plus_one tvar0) in
                    ( t1, [ (T.dummy_label, T.COPY (t1, id1)) ] )

                | S.ARR (id1, exp1) -> let (t1, code1) = translate_exp exp1 in
                    let t2 = ".t" ^ string_of_int (plus_one tvar0) in
                    ( t2, code1 @ [ (T.dummy_label, T.LOAD (t2, (id1, t1))) ] ) 
                )



let rec translate_stmt : S.stmt -> T.linstr list
=fun stmt0 -> match stmt0 with
| S.ASSIGN (lv1, exp1) -> ( match lv1 with
                        | S.ID (id1) -> let (t1, code1) = translate_exp exp1 in
                           code1 @ [ ( T.dummy_label, T.COPY (id1, t1)) ]
              
                        | S.ARR (id1, arr_size1) -> let (t1, code1) = translate_exp arr_size1 in
                                                let (t2, code2) = translate_exp exp1 in
                                                code1 @ code2 @ [ ( T.dummy_label, T.STORE ((id1, t1), t2) ) ]
                         )

| S.IF (exp1, stmt1, stmt2) ->
    let (t1, code1) = translate_exp exp1 in
    let codetrue = translate_stmt stmt1 in
    let codefalse = translate_stmt stmt2 in
    let label_true = plus_one label0 in
	let label_false = plus_one label0 in
	let label_exit = plus_one label0 in
    code1 @ [ (T.dummy_label, T.CJUMP (t1, label_true)) ] @ [ (T.dummy_label, T.UJUMP (label_false)) ] @
    [ (label_true, T.SKIP) ] @ codetrue @ [ (T.dummy_label, T.UJUMP (label_exit)) ] @
    [ (label_false, T.SKIP) ] @ codefalse @ [ (T.dummy_label, T.UJUMP (label_exit)) ] @
    [ (label_exit, T.SKIP) ]

| S.WHILE (exp1, stmt1) -> 
    let (t1, code1) = translate_exp exp1 in
    let codebody = translate_stmt stmt1 in
    let label_entry = plus_one label0 in
    let label_exit = plus_one label0 in
    [ (label_entry, T.SKIP) ] @ code1 @ [ (T.dummy_label, T.CJUMPF (t1, label_exit)) ] @
    codebody @ [ (T.dummy_label, T.UJUMP label_entry) ] @ [ (label_exit, T.SKIP) ]

| S.DOWHILE (stmt1, exp1) -> 
    ( translate_stmt stmt1 ) @ ( translate_stmt ( WHILE (exp1, stmt1) )  )

| S.READ (id1) -> [(T.dummy_label, T.READ id1)]

| S.PRINT (exp1) ->
    let (t1, code1) = translate_exp exp1 in
    code1 @ [ ( T.dummy_label, T.WRITE t1 ) ]

| S.BLOCK (block1) -> (translate_block block1)



and translate_stmts : S.stmts -> T.linstr list
= fun stmts0 -> match stmts0 with
| hd::tl -> ( translate_stmt hd ) @ ( translate_stmts tl )
| [] -> []


and translate_decl : S.decl -> T.linstr
= fun decl0 -> ( match decl0 with
| (type1, id1) -> match type1 with
                | S.TINT -> ( T.dummy_label, T.COPYC(id1, 0) )
                | S.TARR size1 -> ( T.dummy_label, T.ALLOC(id1, size1) )
               )


and translate_decls : S.decls -> T.linstr list
= fun decls0 -> match decls0 with
| hd::tl -> ( translate_decl hd ) :: ( translate_decls tl )
| [] -> [] 


and translate_block : S.block -> T.linstr list
= fun block0 -> match block0 with
| (decls1, stmsts1) -> ( translate_decls decls1 ) @ ( translate_stmts stmsts1 )


let rec translate : S.program -> T.program
=fun s_program0 -> (translate_block s_program0) @ [ (T.dummy_label, T.HALT) ]