
        (declare-sort Value)
        (define-sort Principles () (Array Value Bool))
        (declare-const empty Principles)
        (assert (forall ((v Value)) (not (select empty v))))
        (declare-const public Principles)
        (assert (forall ((v Value)) (select public v)))
        (define-fun insert ((p Principles) (v Value)) Principles (store p v true))
        (echo "Sanity check for preamble. Should be SAT")
        (check-sat)
    (declare-datatypes ((User 0)) (((User (id Value)(pass_hash Value)(name Value)))))
(assert (forall ((a User) (b User)) (=> (= (id a) (id b)) (= a b))))
            (push) 
            (echo "Checking User.pass_hash read")
            
        (define-fun p1 ((r User)) Principles
            empty
        )
    
            
        (define-fun p2 ((r User)) Principles
            (insert empty (id r))
        )
    
            (assert (not (forall ((r User) (v Value)) 
                (=> (select (p2 r) v) (select (p1 r) v))
            )))
            (check-sat)
            (pop)
        
            (push) 
            (echo "Checking User.pass_hash write")
            
        (define-fun p1 ((r User)) Principles
            (insert empty (id r))
        )
    
            
        (define-fun p2 ((r User)) Principles
            (insert empty (id r))
        )
    
            (assert (not (forall ((r User) (v Value)) 
                (=> (select (p2 r) v) (select (p1 r) v))
            )))
            (check-sat)
            (pop)
        
            (push) 
            (echo "Checking User.name read")
            
        (define-fun p1 ((r User)) Principles
            public
        )
    
            
        (define-fun p2 ((r User)) Principles
            public
        )
    
            (assert (not (forall ((r User) (v Value)) 
                (=> (select (p2 r) v) (select (p1 r) v))
            )))
            (check-sat)
            (pop)
        
            (push) 
            (echo "Checking User.name write")
            
        (define-fun p1 ((r User)) Principles
            empty
        )
    
            
        (define-fun p2 ((r User)) Principles
            empty
        )
    
            (assert (not (forall ((r User) (v Value)) 
                (=> (select (p2 r) v) (select (p1 r) v))
            )))
            (check-sat)
            (pop)
        
