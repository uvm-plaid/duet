a logic programming top level layer that read in files and unifies type
variables??

    import gd-pb.ed.duet
    
    m : ℕ[m] ← lvar
    n : ℕ[n] ← lvar
    
    xs : 𝕄 [L∞, U|m, n⋅𝔻 ] ← readCSV "data.csv"
    ys : 𝕄 [L∞, U|m, 1⋅𝔻 ] ← readCSV "labels.csv"
    
    print@(m) -- print length of db
    
    main@[m, n, 0.05 100 0.0001 0.0001 . xs, ys, 0.05, 100, 0.0001, 0.0001, 1]
