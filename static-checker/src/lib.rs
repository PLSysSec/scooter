use policy_lang::ast::*;

pub fn gen_preamble(gp: &GlobalPolicy) -> String {
    let mut out = String::new();
    out += r#"
        (declare-sort Value)
        (define-sort Principles () (Array Value Bool))
        (declare-const empty Principles)
        (assert (forall ((v Value)) (not (select empty v))))
        (declare-const public Principles)
        (assert (forall ((v Value)) (select public v)))
        (define-fun insert ((p Principles) (v Value)) Principles (store p v true))
        (echo "Sanity check for preamble. Should be SAT")
        (check-sat)
    "#;
    for cp in gp.collections.iter() {
        out += &format!("(declare-datatypes (({0} 0)) ((({0} {1}))))\n", &cp.name, gen_fields(&cp));
        out += &format!("(assert (forall ((a {0}) (b {0})) (=> (= (id a) (id b)) (= a b))))", &cp.name);
    }
    out
}

fn gen_fields(cp: &CollectionPolicy) -> String {
    let mut out = String::new();
    out += "(id Value)";
    for (n, _) in cp.fields.iter() {
        out += &format!("({} Value)", &n);
    }
    out
}

fn gen_policy_func(name: &str, type_name: &str, policy: &Policy) -> String {
    let param = match policy {
        Policy::Func(f) => &f.param,
        _ => "r"
    };
    
    format!(r#"
        (define-fun {} (({} {})) Principles
            {}
        )
    "#, name, param, type_name, gen_func_body(policy))
}

fn gen_func_body(p: &Policy) -> String {
    let func = match p {
        Policy::Public => { return "public".into() },
        Policy::None => { return "empty".into() },
        Policy::Func(f) => f
    };

    gen_from_expr(&func.expr)
}

fn gen_from_expr(qe: &QueryExpr) -> String {
    match qe {
        QueryExpr::Or(l, r) => format!("((_ map or) {} {})", gen_from_expr(l), gen_from_expr(r)),
        QueryExpr::Path(p) => {
            let mut iter = p.iter();
            let start = iter.next().unwrap().to_string();
            iter.fold(start, |acc, seg| {
                format!("(insert empty ({} {}))", seg, acc)
            })
        }
    }
}

pub fn gen_full(gp_before: &GlobalPolicy, gp_after: &GlobalPolicy) -> String {
    let mut out = gen_preamble(gp_after);
    for (cp_b, cp_a) in gp_before.collections.iter().zip(gp_after.collections.iter()) {
        out += &gen_collection_checks(cp_b, cp_a);
    }

    out
}

fn gen_collection_checks(cp_before: &CollectionPolicy, cp_after: &CollectionPolicy) -> String {
    let mut out = String::new();
    for f in cp_before.fields.keys() {
        out += &format!(r#"
            (push) 
            (echo "{}")
            {}
            {}
            (assert (not (forall ((r {}) (v Value)) 
                (=> (select (p2 r) v) (select (p1 r) v))
            )))
            (check-sat)
            (pop)
        "#,
        &format!("Checking {}.{} read", &cp_before.name, f),
        gen_policy_func("p1", &cp_before.name, &cp_before.fields[f].read),
        gen_policy_func("p2", &cp_before.name, &cp_after.fields[f].read),
        &cp_after.name)
    }
    out
}

// fn gen_check(cp: &CollectionPolicy, field: &str) -> String {
//     let mut out = format!(r#"
//         (push) 
//         (define-fun p1 ((r {0})) ((p Value))
//             (select {} p)
//         )

//         (define-fun p2 ((r {0})) ((p Value))
//             (select {} p)
//         )
        
//         (assert (not (forall ((u {0}) (v Value)) 
//             (=> (p2 u v) (p1 u v))
//         )))
//     "#, &cp.name, )
// }

#[cfg(test)]
mod tests {
    #[test]
    fn it_works() {
        assert_eq!(2 + 2, 4);
    }
}
