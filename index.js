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
    fix: fn => ({n,id,tags}) =>R.alt(
        R.lit(fn, {n:n+1, id, tags}),
        R.fix(regex => fn(({n,id,tags}) => R.alt(
            R.lit(fn, {n:n+1, id, tags}),
            regex))({n:0, id:fn, tags: null}))),

    lit: chr => ({n,id,tags}) => R.lit(chr, {n:n+1,id,tags}),
    eps: () => ({n,id,tags}) => R.eps({n,id, tags})

// the grammar itself is used as a unique identifer 
// for the start symbol S.
})({n:0,id:gmr,tags:[]})

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
    let stack = [{nfa, v: []}]
    let shift = () => {
        let next = stack[0].nfa.next(str.charAt(idx))
        if(next.size == 0) return false
        stack.unshift({nfa: [...next].reduce(plus, zero), v: [{idx, ch: str.charAt(idx)}, stack[0].v]})
        idx++
        return true
    }
    let reduce = () => {
        let reductions = stack[0].nfa.done()
        if(reductions.size == 0) return false
        if(reductions.size > 1) throw "Reduce/Reduce conflict"
        let {n, id, tags} = [...reductions][0]
        let v = stack[0].v;
        while(0 < n--) stack.shift()
        
        if(tags) {
            let vsub = stack[0].v;
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
        stack.unshift({nfa: [...stack[0].nfa.next(id)].reduce(plus, zero), v})
        return true
    }
    while(idx < str.length) {
        if(!(shift() || reduce())) return false
    }
    do {
        if([...stack[0].nfa.done()].some(
            ({n,id}) => id == S && n == stack.length-1)) {
            return stack[0].v;
        }
    } while(reduce())
    return false;
}

module.exports = {parse, compile, derive};

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
