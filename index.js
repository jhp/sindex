Array.prototype.concatMap = function(fn) {
    let ret = [];
    for(let ii = 0; ii < this.length; ii++) {
        for(let v of fn(this[ii])) {
            ret.push(v);
        }
    }
    return ret;
}

let derive = (gmr) => R => gmr({

    tag: (t, g) => ({n,id,tags}) => 
        R.alt(
            R.lit(g, {n:n+1, id, tags}),
            g({n:0,id:g,tags: [t,null]})),
    
// A | B -> [A] | [B]
    alt: (l,r) => ({n,id,tags}) =>
        R.alt(l({n,id,tags}), r({n,id,tags})),

// AB -> [A] | A[B]
// the function l is used as a unique identifier for A.
    seq: (l,r) => ({n,id,tags}) => 
        R.alt(
            l({n:0,id:l,tags:null}),
            R.seq(R.lit(l), r({n:n+1,id,tags}))),

// (A -> ...A...) -> ([A] -> A | ...(A | [A])...)
    fix: fn => ({n,id,tags}) => R.alt(
        R.lit(fn, {n:n+1, id, tags}),
        R.fix(regex => fn(({n,id,tags}) => R.alt(
            R.lit(fn, {n:n+1, id, tags}),
            regex))({n:0, id:fn, tags: null}))),

    lit: chr => ({n,id,tags}) => R.lit(chr, {n:n+1,id,tags}),
    eps: () => ({n,id,tags}) => R.eps({n,id,tags})

// the grammar itself is used as a unique identifer 
// for the start symbol S.
})({n:0,id:gmr,tags:null})

let add_res = (res, next) => res ?
    plus({done: () => new Set([res]), next: () => new Set()}, next) :
    next;

let zero = ({
    done: () => new Set(),
    next: () => new Set()
})

let plus = (l,r) => {
    let cycle = false
    return {
        done: () => {
            if(cycle) return new Set()
            cycle = true
            let result = new Set([...l.done(), ...r.done()])
            cycle = false
            return result
        },
        next: chr => {
            if(cycle) return new Set()
            cycle = true
            let result = new Set([...l.next(chr), ...r.next(chr)])
            cycle = false
            return result
        }
    };
}

let compile = (re) => re({
    eps: (res) => next => add_res(res, next),
    lit: (chr, res) => next => ({
        done: () => new Set(),
        next: (ch) => new Set(ch === chr ? [add_res(res, next)] : [])
    }),
    seq: (l,r) => next => l(r(next)),
    alt: (l,r) => next => plus(l(next), r(next)),
    fix: (fn) => next => {
        let self = null
        let loop = {
            done: () => self.done(),
            next: (chr) => self.next(chr)
        }
        self = fn(_next => loop)(next)
        return loop
    }
})({done: () => new Set(), next: () => new Set()})

let parse = (S, nfa, str, idx=0) => {
    let stacks = [
        [{nfa, v: null, id: null}, null]
    ];
    let shift = (stack) => {
        let next = stack[0].nfa.next(str.charAt(idx))
        if(next.size == 0) return [];
        let chr = str.charAt(idx);
        return [
            [
                {
                    id: str.charAt(idx),
                    nfa: [...next].reduce(plus, zero),
                    v: [context => chr, stack[0].v]
                    //v: [{idx, ch: str.charAt(idx)}, stack[0].v]
                },
                stack
            ]
        ];
    }
    let reduce = (stack) => {
        let reductions = stack[0].nfa.done()
        return [...reductions].map(({n,id,tags}) => {
            let s = stack;
            let v = stack[0].v;
            while(0 < n--) s = s[1];

            if(tags) {
                let vsub = s[0].v;
                let args = [];
                while(v !== vsub) {
                    args.unshift(v[0]);
                    v = v[1];
                }
                for(let t = tags; t; t = t[1]) {
                    let argfn = (args) => context => t[0](context, ...args.map(arg => arg(context)));
                    args = [argfn(args)];
                }
                v = [args[0], v];
            }
            return [
                {
                    id,
                    nfa: [...s[0].nfa.next(id)].reduce(plus, zero),
                    v
                },
                s
            ];
        });
    }
    function reduce_all() {
        let wset = stacks;
        while(wset.length) {
            wset = wset.concatMap(reduce);
            stacks = [...stacks, ...wset];
        }
        let m = new Map();
        for(let stack of stacks) {
            if(!m.has(stack[0].id)) m.set(stack[0].id, new Map());
            m.get(stack[0].id).set(stack[1], stack);
        }
        stacks = [...m.values()].concatMap(m => m.values());
    }
    while(idx < str.length) {
        reduce_all();
        stacks = stacks.concatMap(shift);
        idx++;
        if(!stacks.length) return false;
    }
    reduce_all();
    console.log("At index", idx, stacks.length);
    let results = stacks
        .map(stack => {
	    let final = [...stack[0].nfa.done()].find(({id}) => id == S);
	    if(!final) return null;
            let args = [];
            for(let v = stack[0].v; v; v = v[1]) {
 		args.unshift(v[0]);
	    }
            for(let t = final.tags; t; t = t[1]) {
                let argfn = (args) => context => t[0](context, ...args.map(arg => arg(context)));
                args = [argfn(args)];
            }
	    return args;
	})
        .filter(Boolean);
    return results;
}

module.exports = {parse, compile, derive};

let gmr_gmr = ({fix, alt, seq, lit, eps, tag}) => {
    function $str(context, chrs) { return chrs.join(''); }
    function $arr(context, elem, elems) { return [elem, ...elems]; }
    // function $arr(context, ...elems) { return ['$arr', ...elems]; }
    function $nil(contect, ...elems) { return []; }
    function $wrap(context, ...elems) { return elems.length === 1 ? elems[0] : elems; }
    // function $wrap(context, ...elems) { return ['$wrap', ...elems]; }
    function $evens(context, elems) { return elems.filter((elem, ii) => ii%2 === 0) }
    //function $evens(context, ...elems) { return ['$evens', ...elems]; }
    function alts(arr) {
        if(arr.length == 1) return arr[0];
        if(arr.length == 2) return alt(arr[0], arr[1]);
        let idx = Math.floor(arr.length / 2);
        return alt(alts(arr.slice(0, idx)), alts(arr.slice(idx)));
    }
    let tag$ = (str, inner) => tag((context, ...args) => context[str](...args), inner);

    let seqs = (...arr) => arr.reduce((l,r) => seq(l,r));
    let many1 = (inner) => fix(m1 => tag($arr,
                                         seq(
                                             tag($wrap, inner),
                                             alt(tag($nil, eps()),
                                                 m1))));
    let many = (inner) => fix(m => alt(
        tag($nil, eps()),
        tag($arr, seq(
            tag($wrap, inner),
            m))));
    let sepBy = (v, sep) => fix(
        lst => tag($arr, seq(tag($wrap, v),
                   alt(tag($nil, eps()),
                       tag($arr, seq(tag($wrap, sep), lst))))));
    let alpha = alts(
        'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'.split('').map(chr => lit(chr))
    );
    let digit = alts(
        '0123456789'.split('').map(chr => lit(chr))
    );
    // does not include \ or " or ]
    let special = alts(
        "`~!@#$%^&*()-_=+[{}|';:/?,<.>".split('').map(chr => lit(chr))
    );
    let ws = alts([lit(' '), lit('\t'), lit('\n')]);
    let symbol = chr => tag((ctxt,l,r) => l, seq(lit(chr), many(ws)));
    let colon = symbol(':');
    let pipe = symbol('|');
    let equal = symbol('=');
    let star = symbol('*');
    let plus = symbol('+');
    let query = symbol('?');
    let lparen = symbol('(');
    let rparen = symbol(')');
    let semi = symbol(';');

    let escaped = chr => tag((ctxt,l,r) => r, seq(lit('\\'), lit(chr)))

    let idfer = tag($str, tag((ctxt,hd,tl) => [hd, ...tl], seqs(alpha, many(alt(alpha, digit)), many(ws))));
    let str = tag((ctxt, l, str) => str,
                  seqs(lit('"'),
                       tag($str, many(alts([alpha, digit, special, lit(']'), escaped('\\'), escaped('"')]))),
                       lit('"'), many(ws)));
    let range = tag((ctxt, l, str) => str,
                    seqs(lit('['),
                         tag($str, many(alts([alpha, digit, special, lit('"'), escaped('\\'), escaped(']')]))),
                         lit(']'), many(ws)));

    let postfix = alts([plus, query, star]);

    let rhs = fix(rhs => {
        let atom = alts([
            tag$('idfer', idfer),
            tag$('range', range),
            tag$('str', str),
            tag$('paren', tag((context, lp, x, rp) => x, seqs(lparen, rhs, rparen)))
        ]);
        let atomPost = tag$('post', seq(atom, alt(eps(), postfix)));
        // TODO: add postfix back
        atomPost = atom;
        let union = tag((ctxt, u) => ctxt.union(u), tag($evens, sepBy(atomPost, pipe)));
        let sum = tag(
            (context, idfer, _colon, atomsHead, atomsTail) => context.sum([[idfer, atomsHead], ...atomsTail]),
            seqs(idfer, colon, tag($evens, sepBy(atomPost, many1(ws))),
                 many(tag(
                     (context, _pipe, idfer, _colon, atoms) => [idfer, atoms],
                     seqs(pipe, idfer, colon, tag($evens, sepBy(atomPost, many1(ws))))))));
        return tag((ctxt, rhs, ws) => rhs, seq(alt(union, sum), many(ws)));
    });
                                
    let defn = tag((ctxt,idfer,_equal,rhs) => ctxt.defn(idfer, rhs), seqs(idfer, equal, rhs, semi));

    // return tag$('top', rhs);
    // return tag$('top', semi);
    //return tag$('top', seq(seq(rhs, many(ws)), semi));
    return tag((ctxt,S,_semi,defns) => ctxt.top(S,defns), seqs(rhs, semi, many(defn)));
}

let str1 = "str: \"abc\" chr* | idf: [abc] ; ";
let str2 = `alpha: alpha | digit: digit;
alpha = [abcdefghijklmnopqrstuvwxyz];
digit = [0123456789];
`;

let str3 = `[abc] | [123] ;`;
//let str1= "\"abc\" | foo*";
str3 = `[abc] | foo; foo = abc: "abc" [def] "ghi" | gkl: "klj" ; `

let results = parse(gmr_gmr, 
                   compile(derive(gmr_gmr)),
                   str3);
let fns = ({
    post: (...args) => ['post', ...args],
    idfer: (...args) => ['idfer', ...args],
    range: (...args) => ['range', ...args],
    str: (...args) => ['str', ...args],
    paren: (...args) => ['paren', ...args],
    union: (...args) => ['union', ...args],
    sum: (...args) => ['sum', ...args],
    defn: (...args) => ['defn', ...args],
    top: (...args) => ['top', ...args]
});

fns = G => ({
    post: null,
    idfer: (name) => env => {
        console.log(name, env);
        return env[name](env)
    },
    range: (chrs) => env => chrs.split('').map(G.lit).reduce(G.alt),
    str: (chrs) => env => chrs.split('').map(G.lit).reduce(G.seq),
    paren: (inner) => env => inner(env),
    union: (alts) => env => alts.map(alt => alt(env)).reduce(G.alt),
    sum: (opts) => env => opts.map(([tag,atoms]) => G.tag((ctxt, ...args) => ctxt[tag](...args), atoms.map(atom => atom(env)).reduce(G.seq))).reduce(G.alt),
    defn: (idfer, rhs) => ({[idfer]: env => G.fix(v => rhs({...env, [idfer]: () => v}))}),
    top: (rhs, defns) => rhs( defns.reduce((l,r) => Object.assign({},l,r), {epsilon: () => G.eps()}) )
});

let parsed_gmr = G => results[0][0](fns(G));

results = parse(parsed_gmr,
                compile(derive(parsed_gmr)),
                'abcdghi');

console.log(results);
console.log(
    JSON.stringify(
        results[0][0]({
            abc: (...args) => ['abc', ...args],
            gkl: (...args) => ['gkl', ...args]
        }), null, 4
    ));
