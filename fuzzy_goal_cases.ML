
val strip_params = map (apfst (perhaps (try Name.dest_skolem))) o Logic.strip_params;

fun extract_fixes NONE prop = (strip_params prop, [])
  | extract_fixes (SOME outline) prop =
      chop (length (Logic.strip_params outline)) (strip_params prop);

val case_conclN = "case";
val case_hypsN = "hyps";
val case_premsN = "prems";

    
fun mapState _ _ [] = [] 
  | mapState f state (x::xs) = 
      let val (state2, x2) = f state x 
      in x2 :: mapState f state2 xs end
  
(* list contains element *)
fun contains [] _ = false
  | contains (x::xs) y = (x = y orelse contains xs y)

fun extract_assumes2 (prop: term) = 
  let 
    val hyps = Logic.strip_assums_hyp prop;
    fun remove_trailing_underscore s =
      let val l = String.explode s
      in 
        if List.last l = #"_" then List.take (l, List.length l - 1)
        else l
      end |> String.implode
    val params = Logic.strip_params prop |> map fst |> map remove_trailing_underscore |> List.rev
    fun make_unique used name i = 
      if i = 2 andalso not (contains used name) then name
      else if contains used (name ^ @{make_string} i) then make_unique used name (1+i)
      else (name ^ @{make_string} i);
    fun remove_dot_h acc [] = rev acc
      | remove_dot_h _   (#"."::xs) = remove_dot_h [] xs
      | remove_dot_h acc (x::xs) = remove_dot_h (x::acc) xs
    val remove_dot = remove_dot_h [];
    fun remove_dot_s s = String.explode s |> remove_dot |> String.implode;
    fun derive_name (de_bruijn_names: string list) (hyp: term) = 
      case hyp of
        Const (n, _) => remove_dot_s n
       | Term.Free (n, _) => n 
       | Var ((s,_), _) => s
       | Bound i  => 
            if i < length de_bruijn_names then List.nth(de_bruijn_names, i) else "bound" ^ @{make_string} i
       | Abs (n,_,b) => derive_name (n::de_bruijn_names) b
       | Const ("HOL.Trueprop", _) $ y => derive_name de_bruijn_names y
       | Const ("HOL.eq", _) $ Free (n, _) $ _ => n ^ "_def"
       | Const ("HOL.eq", _) $ l => derive_name de_bruijn_names l ^ "_eq"
       | Const ("HOL.All", _) $ b => "All_" ^ derive_name de_bruijn_names b
       | Const ("HOL.Ex", _) $ b => "Ex_" ^ derive_name de_bruijn_names b
       | Const ("HOL.Not", _) $ b => "not_" ^ derive_name de_bruijn_names b
       | Const ("HOL.implies", _) $ _ $ b => "implies_" ^ derive_name de_bruijn_names b
       | Const ("HOL.disj", _) $ a $ _ => "cases_" ^ derive_name de_bruijn_names a 
       | x $ _ => derive_name de_bruijn_names x
    fun clean_char c = if Char.isAlphaNum c orelse c = #"'" then c else  #"_"
    
    fun clean_name s = String.explode s |> remove_dot |> map clean_char |> String.implode
    fun extract_name used hyp = make_unique used (derive_name params hyp |> clean_name) 2;
    fun to_named used hyp =
      let val name = extract_name used hyp 
      in (name::used, (name, [hyp])) end;
    val named_hyps = mapState to_named [] hyps;
  in
    (named_hyps, [])
  end


fun dest_binops cs tm =
  let
    val n = length cs;
    fun dest 0 _ = []
      | dest 1 t = [t]
      | dest k (_ $ t $ u) = t :: dest (k - 1) u
      | dest _ _ = raise TERM ("Expected " ^ string_of_int n ^ " binop arguments", [tm]);
  in cs ~~ dest n tm end;

fun bindings args = map (apfst Binding.name) args;


fun app us t = Term.betapplys (t, us);

fun extract_case ctxt (case_outline, raw_prop) concls =
  let
    val props = Logic.dest_conjunctions (Drule.norm_hhf (Proof_Context.theory_of ctxt) raw_prop);
    val len = length props;
    val nested = is_some case_outline andalso len > 1;

    fun extract prop =
      let
        val (fixes1, fixes2) = extract_fixes case_outline prop;
        val abs_fixes = fold_rev Term.abs (fixes1 @ fixes2);
        fun abs_fixes1 t =
          if not nested then abs_fixes t
          else
            fold_rev Term.abs fixes1
              (app (map (Term.dummy_pattern o #2) fixes2) (fold_rev Term.abs fixes2 t));
        val (assumes1, assumes2) =
          extract_assumes2 prop
          |> apply2 (map (apsnd (maps Logic.dest_conjunctions)));

        val concl = Object_Logic.drop_judgment ctxt (Logic.strip_assums_concl prop);
        val binds =
          (case_conclN, concl) :: dest_binops concls concl
          |> map (fn (x, t) => ((x, 0), SOME (abs_fixes t)));
      in
       ((fixes1, map (apsnd (map abs_fixes1)) assumes1),
        ((fixes2, map (apsnd (map abs_fixes)) assumes2), binds))
      end;

    val cases = map extract props;


    fun common_case ((fixes1, assumes1), ((fixes2, assumes2), binds)) =
      Rule_Cases.Case {fixes = bindings (fixes1 @ fixes2),
        assumes = assumes1 @ assumes2, binds = binds, cases = []};
    fun inner_case (_, ((fixes2, assumes2), binds)) =
      Rule_Cases.Case {fixes = bindings fixes2, assumes = assumes2, binds = binds, cases = []};
    fun nested_case ((fixes1, assumes1), _) =
      Rule_Cases.Case {fixes = bindings fixes1, assumes = assumes1, binds = [],
        cases = map string_of_int (1 upto len) ~~ map inner_case cases};
  in
    if len = 0 then NONE
    else if len = 1 then SOME (common_case (hd cases))
    else if is_none case_outline orelse length (distinct (op =) (map fst cases)) > 1 then NONE
    else SOME (nested_case (hd cases))
  end;


fun make ctxt rule_struct prop cases =
  let
    val n = length cases;
    val nprems = Logic.count_prems prop;
    fun add_case ((name, _), concls) (cs, i) =
      ((case try (fn () =>
          (Option.map (curry Logic.nth_prem i) rule_struct, Logic.nth_prem (i, prop))) () of
        NONE => (name, NONE)
      | SOME p => (name, extract_case ctxt p concls)) :: cs, i - 1);
  in fold_rev add_case (drop (Int.max (n - nprems, 0)) cases) ([], n) |> #1 end;

fun update_case _ ("", _) cases = cases
  | update_case _ (name, NONE) cases = Name_Space.del_table name cases
  | update_case context (name, SOME c) cases =
      #2 (Name_Space.define context false (Binding.name name, c) cases);





fun fuzzy_goal_cases_tac case_names : context_tactic =
  fn (ctxt, st) =>
    let
      val names = (if null case_names then map string_of_int (1 upto Thm.nprems_of st) else case_names);
      val info = map (rpair [] o rpair []) names;
      val cases = make ctxt NONE (Thm.prop_of (Rule_Cases.internalize_params st)) info;
    in CONTEXT_CASES cases all_tac (ctxt, st) end;

fun detect_closure_state st =
  (case try Logic.dest_term (Thm.concl_of (perhaps (try Goal.conclude) st)) of
    NONE => false
  | SOME t => Term.is_dummy_pattern t);


val _ =
  Theory.setup 
  (Method.setup \<^binding>\<open>fuzzy_goal_cases\<close> (Scan.lift (Scan.repeat Args.name_token) >> (fn names => fn _ =>
    CONTEXT_METHOD (fn _ => fn (ctxt, st) =>
      (case drop (Thm.nprems_of st) names of
        [] => NONE
      | bad =>
          if detect_closure_state st then NONE
          else
            SOME (fn () => ("Excessive case name(s): " ^ commas_quote (map Token.content_of bad) ^
              Position.here (#1 (Token.range_of bad)))))
      |> (fn SOME msg => Seq.single (Seq.Error msg)
           | NONE => fuzzy_goal_cases_tac (map Token.content_of names) (ctxt, st))))) 
      "bind cases for goals deriving names from terms");