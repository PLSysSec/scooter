use policy_lang::ir::*;
use policy_lang::ast;

pub fn gen_full(gp_before: &ast::GlobalPolicy, gp_after: &ast::GlobalPolicy) -> String {
    let mut ird = extract_types(&gp_before);
    let ir_1 = ird.lower(gp_before);
    let ir_2 = ird.lower(gp_after);

    let mut out = gen_preamble(&ird);

    for c in ird.collections() {
        out += &gen_echo(&c.name().1);
        out += &gen_echo("---------------");
        out += &gen_collection_checks(&ird, c.id, ir_1.collection_policy(c.id), &ir_2.collection_policy(c.id));

        for (fname, did) in c.fields() {
            if fname == "id" {
                continue;
            }
            out += &gen_field_checks(&ird, c.id, ir_1.field_policy(*did), ir_2.field_policy(*did));
        }
    }

    out
}



fn gen_collection_checks(ird: &IrData, cid: Id<Collection>, cp_1: &CollectionPolicy, cp_2: &CollectionPolicy) -> String {
    let mut out = String::new();
    out += &gen_echo("create:");
    out += &gen_policy_check(ird, cid, &cp_1.create, &cp_2.create);
    out += &gen_echo("delete:");
    out += &gen_policy_check(ird, cid, &cp_1.delete, &cp_2.delete);

    out 
}

fn gen_field_checks(ird: &IrData, cid: Id<Collection>, fp_1: &FieldPolicy, fp_2: &FieldPolicy) -> String {
    let mut out = String::new();

    out += &gen_echo("");
    out += &gen_echo(&ird.def(fp_1.field_id).name.1);
    out += &gen_echo("read:");
    out += &gen_policy_check(ird, cid, &fp_1.read, &fp_2.read);
    out += &gen_echo("edit:");
    out += &gen_policy_check(ird, cid, &fp_1.edit, &fp_2.edit);

    out

}

fn gen_policy_check(ird: &IrData, cid: Id<Collection>, fp_1: &Policy, fp_2: &Policy) -> String {
    format!(
        r#"
            (push) 
            {}
            {}
            (assert (not (forall ((r {}) (v Value))
                (=> (select (p_after r) v) (select (p_before r) v))
            )))
            (check-sat)
            (pop)
        "#,
        gen_policy(ird, "p_before", cid, &fp_1),
        gen_policy(ird, "p_after", cid, &fp_2),
        mangled_ident(&ird.collection(cid).name)
    )
}

fn gen_policy(ird: &IrData, fn_name: &str, cid: Id<Collection>, policy: &Policy) -> String {
    let mut out = String::new();

    let param = match policy {
        Policy::Func(f) => mangled_ident(&ird.def(f.param).name),
        // Note, this is safe because it won't conflict, but yikes is it scary
        _ => "r".to_string(),
    };

    let body = match policy {
        Policy::Func(pf) => gen_query_expr(ird, pf.body),
        Policy::Public => "public".to_string(),
        Policy::None => "empty".to_string(),
    };

    out += &format!(
        r#"
        (define-fun {} (({} {})) Principles
            {}
        )
        "#,
        fn_name,
        param,
        mangled_ident(&ird.collection(cid).name),
        body
    );

    out
}

fn gen_query_expr(ird: &IrData, eid: Id<Expr>) -> String {
    let expr = ird.expr(eid);
    match expr.kind {
        ExprKind::Or(l, r) => format!("((_ map or) {} {})", gen_query_expr(ird, l), gen_query_expr(ird, r)),
        ExprKind::Var(_) => unimplemented!("We don't parse this yet"),
        ExprKind::Path(obj, field) => {
            format!("(insert empty ({} {}))", mangled_ident(&ird.def(field).name), mangled_ident(&ird.def(obj).name))
        }
    }
}

fn gen_preamble(ird: &IrData) -> String {
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

    for c in ird.collections() {
        let fs: String = c.fields().map(|(_, f)| gen_field(ird, *f)).collect();

        out += &format!( 
            "(declare-datatypes (({0} 0)) ((({0} {1}))))\n",
            mangled_ident(&c.name),
            fs
        );

        out += &format!(
            "(assert (forall ((a {0}) (b {0})) (=> (= ({1} a) ({1} b)) (= a b))))",
            mangled_ident(&c.name),
            mangled_ident(&ird.field(c.id, "id").name)
        );
    }

    out
}

fn gen_field(ird: &IrData, f: Id<Def>) -> String {
    let def = ird.def(f);

    format!("({} Value)", mangled_ident(&def.name))
}

fn mangled_ident(ident: &Ident) -> String {
    format!("i_{}_{}", ident.0, ident.1)
}

fn gen_echo(msg: &str) -> String {
    format!("(echo \"{}\")",  msg)
}