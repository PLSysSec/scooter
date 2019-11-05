use policy_lang::ir;
use policy_lang::ast;

pub fn gen_full(gp_before: ast::GlobalPolicy<String>, gp_after: ast::GlobalPolicy<String>) -> String {
    let mut tcx = ir::extract_types(&gp_before);
    let res_b = ir::resolve(&mut tcx, gp_before);
    let res_a = ir::resolve(&mut tcx, gp_after);


    let mut out = gen_preamble(&mut tcx);

    for (tid, cp_b) in res_b
    {
        out += &gen_collection_checks(&mut tcx, &cp_b, &res_a[&tid]);
    }

    out
}


fn gen_preamble(tcx: &mut ir::TyCtx) -> String {
    let mut out = String::new();

    out += &format!( r#"
        (declare-sort Value)
        (define-sort Principles () (Array Value Bool))
        (declare-const empty Principles)
        (assert (forall ((v Value)) (not (select empty v))))
        (declare-const public Principles)
        (assert (forall ((v Value)) (select public v)))
        (define-fun insert ((p Principles) (v Value)) Principles (store p v true))
        (echo "Sanity check for preamble. Should be SAT")
        (check-sat)
    "#);

    for c in tcx.collections() {
        let fs: String = c.fields.values().map(|f| gen_field(tcx, f)).collect();
        out += &format!(
            "(declare-datatypes (({0} 0)) ((({0} {1}))))\n",
            mangled_ident(tcx, c.name),
            fs
        );

        out += &format!(
            "(assert (forall ((a {0}) (b {0})) (=> (= ({1} a) ({1} b)) (= a b))))",
            mangled_ident(tcx, c.name),
            mangled_ident(tcx, c.fields["id"].ident())
        );
    }

    out
}

fn gen_collection_checks(tcx: &ir::TyCtx, cp_b: &ir::CollectionPolicy, cp_a: &ir::CollectionPolicy) -> String {
    assert_eq!(cp_a.type_id, cp_b.type_id, "{:?}\n~~~\n{:?}", tcx.get_type(cp_a.type_id), tcx.get_type(cp_b.type_id));
    let coll_tid = cp_a.type_id;

    let mut out = String::new();

    let coll = match tcx.get_type(coll_tid) {
        ir::Type::Collection(c) => c,
        _ => unreachable!("Malformed policy")
    };

    for (n, f) in coll.fields.iter() {
        if n == "id" {
            continue;
        }
        out += &gen_policy_check(tcx, coll.name, mangled_ident(tcx, f.ident()), &cp_b.fields[&f.ident()].read, &cp_a.fields[&f.ident()].read);
        out += &gen_policy_check(tcx, coll.name, mangled_ident(tcx, f.ident()), &cp_b.fields[&f.ident()].write, &cp_a.fields[&f.ident()].write);
    }
    out += &gen_policy_check(tcx, coll.name, "create".to_string(), &cp_b.create_policy, &cp_a.create_policy);
    out += &gen_policy_check(tcx, coll.name, "delete".to_string(), &cp_b.delete_policy, &cp_a.delete_policy);

    out
}

fn gen_policy_check(tcx: &ir::TyCtx, coll_type_name: ir::IdentId, f_str: String, fp_b: &ir::Policy, fp_a: &ir::Policy) -> String {
    format!(
        r#"
            (push)
            (echo "Checking {}")
            {}
            {}
            (assert (not (forall ((r {}) (v Value))
                (=> (select (p_after r) v) (select (p_before r) v))
            )))
            (check-sat)
            (pop)
        "#,
        f_str,
        gen_policy(tcx, "p_before", coll_type_name, &fp_b),
        gen_policy(tcx, "p_after", coll_type_name, &fp_a),
        mangled_ident(tcx, coll_type_name)
    )
}

fn gen_policy(tcx: &ir::TyCtx, fn_name: &str, type_name: ir::IdentId, policy: &ir::Policy) -> String {
    let mut out = String::new();

    let param = match policy {
        ir::Policy::Func(f) => mangled_ident(tcx, f.param),
        // Note, this is safe because it won't conflict, but yikes is it scary
        _ => "r".to_string(),
    };

    let body = match policy {
        ast::Policy::Func(pf) => gen_query_expr(tcx, &pf.expr),
        ast::Policy::Public => "public".to_string(),
        ast::Policy::None => "empty".to_string(),
    };

    out += &format!(
        r#"
        (define-fun {} (({} {})) Principles
            {}
        )
        "#,
        fn_name,
        param,
        mangled_ident(tcx, type_name),
        body
    );

    out
}

fn gen_query_expr(tcx: &ir::TyCtx, qe: &ir::QueryExpr) -> String {
    match qe {
        ir::QueryExpr::Or(l, r) => format!("((_ map or) {} {})", gen_query_expr(tcx, l), gen_query_expr(tcx, r)),
        ir::QueryExpr::Path(p) => {
            let mut iter = p.iter();
            let start = mangled_ident(tcx, *iter.next().unwrap());
            // TODO: This is silly since paths can only be of length two
            iter.fold(start, |acc, seg| {
                format!("(insert empty ({} {}))", mangled_ident(tcx, *seg), acc)
            })
        }
    }
}

fn gen_field(tcx: &ir::TyCtx, f: &ir::Field) -> String {
    match tcx.get_type(f.type_id()) {
        ir::Type::Prim(ir::Prim::Any) => format!("({} Value)", mangled_ident(tcx, f.ident())),

        _ => panic!("Malformed type")
    }
}

fn mangled_ident(tcx: &ir::TyCtx, id: ir::IdentId) -> String {
    let i: usize = id.into();
    format!("i_{}_{}", i, tcx.get_ident(id).raw())
}
