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
        g({n,id,tags: [t,tags]}),
    
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
    eps: () => ({n,id,tags}) => R.eps({n,id, tags})

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

let parse = (S, nfa, str, idx=0) => fns => {
    let stacks = [
        [{nfa, v: [], id: null}, null]
    ];
    let shift = (stack) => {
        let next = stack[0].nfa.next(str.charAt(idx))
        if(next.size == 0) return [];
        return [
            [
                {
                    id: str.charAt(idx),
                    nfa: [...next].reduce(plus, zero),
                    v: [{idx, ch: str.charAt(idx)}, stack[0].v]
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
                    args = [fns[t[0]]( ...args )];
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
        console.log("At index", idx, stacks.length);
        if(!stacks.length) return false;
    }
    reduce_all();
    let results = stacks
        .filter(stack => 
                [...stack[0].nfa.done()].some(({id}) => id == S)
               ).map(stack => stack[0].v);
    return results;
}

module.exports = {parse, compile, derive};


let gmr_gmr = ({fix, alt, seq, lit, eps, tag}) => {
    function alts(arr) {
        if(arr.length == 1) return arr[0];
        if(arr.length == 2) return alt(arr[0], arr[1]);
        let idx = Math.floor(arr.length / 2);
        return alt(alts(arr.slice(0, idx)), alts(arr.slice(idx)));
    }
    let seqs = (...arr) => arr.reduce((l,r) => seq(l,r));
    let many1 = (inner) => fix(m1 => tag('$arr', seq(inner, alt(eps(), m1))));
    let many = (inner) => fix(m => alt(eps(), tag('$arr', seq(inner, m))));
    let sepBy = (v, sep) => fix(lst => seq(v, alt(eps(), seq(sep, lst))));
    let alpha = alts(
        'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz'.split('').map(chr => lit(chr))
    );
    let ws = alts([lit(' '), lit('\t'), lit('\n')]);
    let symbol = chr => seq(lit(chr), many(ws));
    let colon = symbol(':');
    let pipe = symbol('|');
    let equal = symbol('=');
    let star = symbol('*');
    let plus = symbol('+');
    let query = symbol('?');
    let lparen = symbol('(');
    let rparen = symbol(')');
    let semi = symbol(';');

    let idfer = seq(many1(alpha), many(ws));
    let str = seqs(lit('"'), many(alpha), lit('"'), many(ws));
    let range = seqs(lit('['), many(alpha), lit(']'), many(ws));

    let postfix = alts([plus, query, star]);

    let rhs = fix(rhs => {
        let atom = alts([
            tag('idfer', idfer),
            tag('range', range),
            tag('str', str),
            tag('paren', seq(lparen, rhs, rparen))
        ]);
        let atomPost = tag('post', seq(atom, alt(eps(), postfix)));
        let union = seqs(sepBy(atomPost, ws), many(seq(pipe, sepBy(atomPost, ws))));
        let sum = seqs(idfer, colon, sepBy(atomPost, ws), many(seqs(pipe, idfer, colon, sepBy(atomPost, ws))));
        return alt(tag("union", union), tag("sum", sum))
    });

    let defn = seqs(idfer, equal, rhs, semi);

    return seqs(rhs, semi, many(defn));
}

let str1 = "str: \"abc\" chr* | idf: [abc] ; ";
//let str1= "\"abc\" | foo*";

let result = parse(gmr_gmr, 
                   compile(derive(gmr_gmr)),
                   str1)({
                       post: (...args) => ['post', ...args],
                       idfer: (...args) => ['idfer', ...args],
                       range: (...args) => ['range', ...args],
                       str: (...args) => ['str', ...args],
                       paren: (...args) => ['paren', ...args],
                       union: (...args) => ['union', ...args],
                       sum: (...args) => ['sum', ...args],
                       '$arr': (elem, arr) => [elem, ...(arr || [])]
                   })
console.log(
    JSON.stringify(
        result && result[0], null, 4
    ));

console.log("Results", result && result.length);
/*

let test_grammar = ({fix, alt, seq, lit, eps, tag}) =>
    fix((A) => alt(
        tag('PARENS', seq(seq(lit('('), A), lit(')'))),
        tag('A', lit('a'))))

console.log(
    JSON.stringify(
        parse(test_grammar, 
              compile(derive(test_grammar)),
              "(((a)))")({
                  PARENS: (...args) => ['PARENS', ...args],
                  A: (...args) => ['A', ...args]
              })
        ,null, 4
    ));

*/
