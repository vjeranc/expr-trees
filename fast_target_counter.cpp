#include <bits/stdc++.h>
#include <boost/unordered/unordered_flat_map.hpp>
#include <boost/unordered/unordered_flat_set.hpp>
using namespace std;

struct Opt {
	int n= 9;
	char mode= 'a'; // a,b,c
	long long target= 100;
	long long max_abs= 1000000000LL;
	string c_style= "errata"; // errata|old
};

static void usage(const char *p) {
	cerr << "Usage: " << p
			 << " [--n 9] [--mode a|b|c] [--target 100] [--max-abs 1000000000] "
					"[--c-style errata|old]\n";
	exit(1);
}

static Opt parse_args(int argc, char **argv) {
	Opt o;
	for(int i= 1; i < argc; i++) {
		string a= argv[i];
		if(a == "--n") {
			if(i + 1 >= argc) usage(argv[0]);
			o.n= stoi(argv[++i]);
		} else if(a == "--mode") {
			if(i + 1 >= argc) usage(argv[0]);
			o.mode= argv[++i][0];
		} else if(a == "--target") {
			if(i + 1 >= argc) usage(argv[0]);
			o.target= stoll(argv[++i]);
		} else if(a == "--max-abs") {
			if(i + 1 >= argc) usage(argv[0]);
			o.max_abs= stoll(argv[++i]);
		} else if(a == "--c-style") {
			if(i + 1 >= argc) usage(argv[0]);
			o.c_style= argv[++i];
		} else
			usage(argv[0]);
	}
	if(o.n < 1 || o.n > 9) {
		cerr << "n must be 1..9\n";
		exit(1);
	}
	if(o.mode != 'a' && o.mode != 'b' && o.mode != 'c') {
		cerr << "mode must be a|b|c\n";
		exit(1);
	}
	if(o.c_style != "errata" && o.c_style != "old") {
		cerr << "c-style must be errata|old\n";
		exit(1);
	}
	return o;
}

static inline __int128 iabs128(__int128 x) { return x < 0 ? -x : x; }
static inline uint64_t uabs64(long long x) {
	return x < 0 ? (uint64_t)(-(x + 1)) + 1ULL : (uint64_t)x;
}
static inline uint64_t gcd64(uint64_t a, uint64_t b) {
	while(b) {
		uint64_t t= a % b;
		a= b;
		b= t;
	}
	return a == 0 ? 1 : a;
}
static inline __int128 gcd128(__int128 a, __int128 b) {
	a= iabs128(a);
	b= iabs128(b);
	while(b) {
		__int128 t= a % b;
		a= b;
		b= t;
	}
	return a == 0 ? 1 : a;
}
static inline bool fits_i64(__int128 x) {
	return x >= (__int128)LLONG_MIN && x <= (__int128)LLONG_MAX;
}

struct Frac {
	long long n= 0, d= 1;
	bool set(__int128 nn, __int128 dd) {
		if(dd == 0) return false;
		if(dd < 0) {
			dd= -dd;
			nn= -nn;
		}
		if(nn == 0) {
			n= 0;
			d= 1;
			return true;
		}
		if(fits_i64(nn) && fits_i64(dd)) {
			long long n64= (long long)nn;
			long long d64= (long long)dd;
			uint64_t g= gcd64(uabs64(n64), uabs64(d64));
			n64/= (long long)g;
			d64/= (long long)g;
			if(d64 < 0) {
				d64= -d64;
				n64= -n64;
			}
			n= n64;
			d= d64;
			return true;
		}
		__int128 g= gcd128(nn, dd);
		nn/= g;
		dd/= g;
		if(dd < 0) {
			dd= -dd;
			nn= -nn;
		}
		if(!fits_i64(nn) || !fits_i64(dd)) return false;
		n= (long long)nn;
		d= (long long)dd;
		return true;
	}
	bool operator==(const Frac &o) const { return n == o.n && d == o.d; }
	bool operator<(const Frac &o) const { return n != o.n ? n < o.n : d < o.d; }
};

struct FracHash {
	size_t operator()(const Frac &x) const noexcept {
		uint64_t a= (uint64_t)x.n, b= (uint64_t)x.d;
		uint64_t h= a ^ (b + 0x9e3779b97f4a7c15ULL + (a << 6) + (a >> 2));
		return (size_t)h;
	}
};

static inline bool in_cap(const Frac &v, long long cap) {
	return llabs(v.n) <= cap && v.d <= cap;
}
static inline bool addf(const Frac &a, const Frac &b, Frac &out) {
	return out.set((__int128)a.n * b.d + (__int128)b.n * a.d,
								 (__int128)a.d * b.d);
}
static inline bool subf(const Frac &a, const Frac &b, Frac &out) {
	return out.set((__int128)a.n * b.d - (__int128)b.n * a.d,
								 (__int128)a.d * b.d);
}
static inline bool mulf(const Frac &a, const Frac &b, Frac &out) {
	return out.set((__int128)a.n * b.n, (__int128)a.d * b.d);
}
static inline bool divf(const Frac &a, const Frac &b, Frac &out) {
	if(b.n == 0) return false;
	return out.set((__int128)a.n * b.d, (__int128)a.d * b.n);
}

enum NT { NUM= 0, FAC= 1, TERM= 2, SUM= 3, PROD= 4, QUOT= 5, EXPR= 6, NTN= 7 };

struct Ctx {
	Opt opt;
	int n;
	vector<array<vector<Frac>, NTN>> values;
	vector<array<boost::unordered_flat_set<Frac, FracHash>, NTN>> value_sets;
	vector<array<char, NTN>> built;

	struct Key {
		int id;
		unsigned char nt;
		Frac v;
		bool operator==(const Key &o) const {
			return id == o.id && nt == o.nt && v == o.v;
		}
	};
	struct KeyHash {
		size_t operator()(const Key &k) const noexcept {
			uint64_t h= (uint64_t)k.id * 1315423911u ^ (uint64_t)k.nt * 2654435761u;
			uint64_t a= (uint64_t)k.v.n, b= (uint64_t)k.v.d;
			h^= a + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
			h^= b + 0x9e3779b97f4a7c15ULL + (h << 6) + (h >> 2);
			return (size_t)h;
		}
	};
	boost::unordered_flat_map<Key, unsigned long long, KeyHash> memo;
	boost::unordered_flat_map<int, unsigned long long> fac_total_cache;
	unsigned long long cases_considered= 0;

	explicit Ctx(const Opt &o)
			: opt(o), n(o.n), values(n * (n + 1) / 2), value_sets(n * (n + 1) / 2),
				built(n * (n + 1) / 2, array<char, NTN>{}) {
		memo.reserve(1 << 20);
		fac_total_cache.reserve(n * n);
	}

	static int cid(int i, int j, int n) {
		return i * (2 * n - i + 1) / 2 + (j - i - 1);
	}
	int id(int i, int j) const { return cid(i, j, n); }

	long long token_value(int i, int j) const {
		long long v= 0;
		for(int k= i + 1; k <= j; k++) v= v * 10 + k;
		return v;
	}

	static long long pow10ll(int t) {
		long long p= 1;
		while(t--) p*= 10;
		return p;
	}

	vector<Frac> gen_atoms(int i, int j) const {
		vector<Frac> out;
		int L= j - i;
		if(opt.mode == 'a') {
			if(L == 1) {
				Frac f;
				f.set(i + 1, 1);
				if(in_cap(f, opt.max_abs)) out.push_back(f);
			}
			return out;
		}
		long long v= token_value(i, j);
		Frac f;
		if(f.set(v, 1) && in_cap(f, opt.max_abs)) out.push_back(f);
		if(opt.mode == 'c') {
			if(opt.c_style == "old") {
				Frac g;
				if(g.set(v, pow10ll(L)) && in_cap(g, opt.max_abs)) out.push_back(g);
			} else {
				for(int t= 1; t <= L; t++) {
					Frac g;
					if(g.set(v, pow10ll(t)) && in_cap(g, opt.max_abs)) out.push_back(g);
				}
			}
		}
		sort(out.begin(), out.end());
		out.erase(unique(out.begin(), out.end(),
										 [](const Frac &a, const Frac &b) { return a == b; }),
							out.end());
		return out;
	}

	void add_unique(int c, int nt, const Frac &v) {
		auto &s= value_sets[c][nt];
		auto ins= s.insert(v);
		if(ins.second) values[c][nt].push_back(v);
	}

	const vector<Frac> &get_values(int i, int j, int nt) {
		int c= id(i, j);
		if(built[c][nt]) return values[c][nt];
		built[c][nt]= 1;
		auto &out= values[c][nt];
		auto &out_set= value_sets[c][nt];

		if(nt == NUM) {
			out_set.reserve((size_t)(j - i + 2));
			for(const auto &v: gen_atoms(i, j)) add_unique(c, nt, v);
			return out;
		}
		if(nt == FAC) {
			const auto &s= get_values(i, j, SUM);
			out_set.reserve(get_values(i, j, NUM).size() + s.size() + 8);
			for(const auto &v: get_values(i, j, NUM)) add_unique(c, nt, v);
			for(const auto &v: s) add_unique(c, nt, v);
			return out;
		}
		if(nt == TERM) {
			const auto &p= get_values(i, j, PROD);
			const auto &q= get_values(i, j, QUOT);
			out_set.reserve(get_values(i, j, NUM).size() + p.size() + q.size() + 8);
			for(const auto &v: get_values(i, j, NUM)) add_unique(c, nt, v);
			for(const auto &v: p) add_unique(c, nt, v);
			for(const auto &v: q) add_unique(c, nt, v);
			return out;
		}
		if(nt == EXPR) {
			const auto &s= get_values(i, j, SUM);
			const auto &p= get_values(i, j, PROD);
			const auto &q= get_values(i, j, QUOT);
			out_set.reserve(get_values(i, j, NUM).size() + s.size() + p.size() +
											q.size() + 8);
			for(const auto &v: get_values(i, j, NUM)) add_unique(c, nt, v);
			for(const auto &v: s) add_unique(c, nt, v);
			for(const auto &v: p) add_unique(c, nt, v);
			for(const auto &v: q) add_unique(c, nt, v);
			return out;
		}

		Frac v;
		if(nt == SUM) {
			size_t est= 0;
			for(int k= i + 1; k < j; k++) {
				const auto &lt= get_values(i, k, TERM);
				const auto &ls= get_values(i, k, SUM);
				const auto &rt= get_values(k, j, TERM);
				est+= (lt.size() + ls.size()) * rt.size() * 2;
			}
			out_set.reserve(est + 16);
			for(int k= i + 1; k < j; k++) {
				const auto &lt= get_values(i, k, TERM);
				const auto &ls= get_values(i, k, SUM);
				const auto &rt= get_values(k, j, TERM);
				for(const auto &a: lt)
					for(const auto &b: rt) {
						if(addf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
						if(subf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
					}
				for(const auto &a: ls)
					for(const auto &b: rt) {
						if(addf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
						if(subf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
					}
			}
			return out;
		}
		if(nt == PROD) {
			size_t est= 0;
			for(int k= i + 1; k < j; k++) {
				const auto &lf= get_values(i, k, FAC);
				const auto &lp= get_values(i, k, PROD);
				const auto &lq= get_values(i, k, QUOT);
				const auto &rf= get_values(k, j, FAC);
				est+= (lf.size() + lp.size() + lq.size()) * rf.size();
			}
			out_set.reserve(est + 16);
			for(int k= i + 1; k < j; k++) {
				const auto &lf= get_values(i, k, FAC);
				const auto &lp= get_values(i, k, PROD);
				const auto &lq= get_values(i, k, QUOT);
				const auto &rf= get_values(k, j, FAC);
				for(const auto &a: lf)
					for(const auto &b: rf) {
						if(mulf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
					}
				for(const auto &a: lp)
					for(const auto &b: rf) {
						if(mulf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
					}
				for(const auto &a: lq)
					for(const auto &b: rf) {
						if(mulf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
					}
			}
			return out;
		}
		// QUOT
		size_t est= 0;
		for(int k= i + 1; k < j; k++) {
			const auto &lf= get_values(i, k, FAC);
			const auto &lp= get_values(i, k, PROD);
			const auto &lq= get_values(i, k, QUOT);
			const auto &rf= get_values(k, j, FAC);
			est+= (lf.size() + lp.size() + lq.size()) * rf.size();
		}
		out_set.reserve(est + 16);
		for(int k= i + 1; k < j; k++) {
			const auto &lf= get_values(i, k, FAC);
			const auto &lp= get_values(i, k, PROD);
			const auto &lq= get_values(i, k, QUOT);
			const auto &rf= get_values(k, j, FAC);
			for(const auto &a: lf)
				for(const auto &b: rf) {
					if(divf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
				}
			for(const auto &a: lp)
				for(const auto &b: rf) {
					if(divf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
				}
			for(const auto &a: lq)
				for(const auto &b: rf) {
					if(divf(a, b, v) && in_cap(v, opt.max_abs)) add_unique(c, nt, v);
				}
		}
		return out;
	}

	bool contains(int i, int j, int nt, const Frac &v) {
		int c= id(i, j);
		return value_sets[c][nt].find(v) != value_sets[c][nt].end();
	}

	unsigned long long fac_total(int i, int j) {
		int c= id(i, j);
		if(auto it= fac_total_cache.find(c); it != fac_total_cache.end())
			return it->second;
		unsigned long long s= 0;
		const auto &fv= get_values(i, j, FAC);
		for(const auto &b: fv) s+= count_state(i, j, FAC, b);
		fac_total_cache.emplace(c, s);
		return s;
	}

	unsigned long long count_state(int i, int j, int nt, const Frac &v) {
		Key key{id(i, j), (unsigned char)nt, v};
		if(auto it= memo.find(key); it != memo.end()) return it->second;

		unsigned long long total= 0;

		if(nt == NUM) {
			int L= j - i;
			if(opt.mode == 'a') {
				if(L == 1) {
					Frac d;
					d.set(i + 1, 1);
					if(d == v) total= 1;
				}
			} else {
				long long val= token_value(i, j);
				Frac f;
				f.set(val, 1);
				if(f == v) total+= 1;
				if(opt.mode == 'c') {
					if(opt.c_style == "old") {
						Frac g;
						g.set(val, pow10ll(L));
						if(g == v) total+= 1;
					} else {
						for(int t= 1; t <= L; t++) {
							Frac g;
							g.set(val, pow10ll(t));
							if(g == v) total+= 1;
						}
					}
				}
			}
		} else if(nt == EXPR) {
			total+= count_state(i, j, NUM, v);
			total+= count_state(i, j, SUM, v);
			total+= count_state(i, j, PROD, v);
			total+= count_state(i, j, QUOT, v);
		} else if(nt == TERM) {
			total+= count_state(i, j, NUM, v);
			total+= count_state(i, j, PROD, v);
			total+= count_state(i, j, QUOT, v);
		} else if(nt == FAC) {
			total+= count_state(i, j, NUM, v);
			total+= count_state(i, j, SUM, v);
		} else if(nt == SUM) {
			Frac b;
			for(int k= i + 1; k < j; k++) {
				unsigned long long part= 0;
				const auto &lt= get_values(i, k, TERM);
				const auto &ls= get_values(i, k, SUM);
				const auto &rt= get_values(k, j, TERM);
				boost::unordered_flat_map<Frac, unsigned long long, FracHash>
						rterm_cache;
				rterm_cache.reserve(rt.size() * 2 + 8);
				auto rterm_count= [&](const Frac &x) -> unsigned long long {
					if(auto it= rterm_cache.find(x); it != rterm_cache.end())
						return it->second;
					unsigned long long c= count_state(k, j, TERM, x);
					rterm_cache.emplace(x, c);
					return c;
				};
				if(rt.size() == 1) {
					const Frac rb= rt[0];
					unsigned long long rc= rterm_count(rb);
					Frac a;
					cases_considered++;
					if(subf(v, rb, a) && contains(i, k, TERM, a))
						part+= count_state(i, k, TERM, a) * rc;
					cases_considered++;
					if(addf(v, rb, a) && contains(i, k, TERM, a))
						part+= count_state(i, k, TERM, a) * rc;
					cases_considered++;
					if(subf(v, rb, a) && contains(i, k, SUM, a))
						part+= count_state(i, k, SUM, a) * rc;
					cases_considered++;
					if(addf(v, rb, a) && contains(i, k, SUM, a))
						part+= count_state(i, k, SUM, a) * rc;
					total+= part;
					continue;
				}
				if(lt.size() <= rt.size()) {
					for(const auto &a: lt) {
						cases_considered++;
						if(subf(v, a, b) && contains(k, j, TERM, b))
							part+= count_state(i, k, TERM, a) * rterm_count(b);
						cases_considered++;
						if(subf(a, v, b) && contains(k, j, TERM, b))
							part+= count_state(i, k, TERM, a) * rterm_count(b);
					}
				} else {
					for(const auto &rb: rt) {
						Frac a;
						cases_considered++;
						if(subf(v, rb, a) && contains(i, k, TERM, a))
							part+= count_state(i, k, TERM, a) * rterm_count(rb);
						cases_considered++;
						if(addf(v, rb, a) && contains(i, k, TERM, a))
							part+= count_state(i, k, TERM, a) * rterm_count(rb);
					}
				}
				if(ls.size() <= rt.size()) {
					for(const auto &s: ls) {
						cases_considered++;
						if(subf(v, s, b) && contains(k, j, TERM, b))
							part+= count_state(i, k, SUM, s) * rterm_count(b);
						cases_considered++;
						if(subf(s, v, b) && contains(k, j, TERM, b))
							part+= count_state(i, k, SUM, s) * rterm_count(b);
					}
				} else {
					for(const auto &rb: rt) {
						Frac s;
						cases_considered++;
						if(subf(v, rb, s) && contains(i, k, SUM, s))
							part+= count_state(i, k, SUM, s) * rterm_count(rb);
						cases_considered++;
						if(addf(v, rb, s) && contains(i, k, SUM, s))
							part+= count_state(i, k, SUM, s) * rterm_count(rb);
					}
				}
				total+= part;
			}
		} else if(nt == PROD) {
			Frac b;
			for(int k= i + 1; k < j; k++) {
				unsigned long long part= 0;
				const auto &rf= get_values(k, j, FAC);
				boost::unordered_flat_map<Frac, unsigned long long, FracHash>
						rfac_cache;
				rfac_cache.reserve(rf.size() * 2 + 8);
				auto rfac_count= [&](const Frac &x) -> unsigned long long {
					if(auto it= rfac_cache.find(x); it != rfac_cache.end())
						return it->second;
					unsigned long long c= count_state(k, j, FAC, x);
					rfac_cache.emplace(x, c);
					return c;
				};
				if(rf.size() == 1 && rf[0].n != 0) {
					const Frac rb= rf[0];
					unsigned long long rc= rfac_count(rb);
					auto back_single= [&](int lnt) {
						const auto &lv= get_values(i, k, lnt);
						Frac a;
						cases_considered++;
						if(divf(v, rb, a) && contains(i, k, lnt, a)) {
							part+= count_state(i, k, lnt, a) * rc;
						}
					};
					back_single(FAC);
					back_single(PROD);
					back_single(QUOT);
					total+= part;
					continue;
				}
				unsigned long long rf_total= 0;
				bool rf_total_ready= false;
				auto back= [&](int lnt) {
					const auto &lv= get_values(i, k, lnt);
					for(const auto &a: lv) {
						if(a.n == 0) {
							// For a*b=v with a=0, solutions exist iff v=0; then any b is
							// valid.
							cases_considered++;
							if(v.n == 0) {
								unsigned long long lc= count_state(i, k, lnt, a);
								if(!rf_total_ready) {
									rf_total= fac_total(k, j);
									rf_total_ready= true;
								}
								part+= lc * rf_total;
							}
							continue;
						}
						cases_considered++;
						if(divf(v, a, b) && contains(k, j, FAC, b))
							part+= count_state(i, k, lnt, a) * rfac_count(b);
					}
				};
				back(FAC);
				back(PROD);
				back(QUOT);
				total+= part;
			}
		} else if(nt == QUOT) {
			Frac a;
			for(int k= i + 1; k < j; k++) {
				unsigned long long part= 0;
				const auto &rf= get_values(k, j, FAC);
				boost::unordered_flat_map<Frac, unsigned long long, FracHash>
						rfac_cache;
				rfac_cache.reserve(rf.size() * 2 + 8);
				auto rfac_count= [&](const Frac &x) -> unsigned long long {
					if(auto it= rfac_cache.find(x); it != rfac_cache.end())
						return it->second;
					unsigned long long c= count_state(k, j, FAC, x);
					rfac_cache.emplace(x, c);
					return c;
				};
				if(rf.size() == 1) {
					const Frac rb= rf[0];
					if(rb.n == 0) continue;
					unsigned long long rc= rfac_count(rb);
					auto back_single= [&](int lnt) {
						const auto &lv= get_values(i, k, lnt);
						cases_considered++;
						if(mulf(v, rb, a) && contains(i, k, lnt, a)) {
							part+= count_state(i, k, lnt, a) * rc;
						}
					};
					back_single(FAC);
					back_single(PROD);
					back_single(QUOT);
					total+= part;
					continue;
				}
				auto back= [&](int lnt) {
					const auto &lv= get_values(i, k, lnt);
					for(const auto &b: rf) {
						if(b.n == 0) continue;
						cases_considered++;
						if(mulf(v, b, a) && contains(i, k, lnt, a))
							part+= count_state(i, k, lnt, a) * rfac_count(b);
					}
				};
				back(FAC);
				back(PROD);
				back(QUOT);
				total+= part;
			}
		}

		memo.emplace(key, total);
		return total;
	}
};

int main(int argc, char **argv) {
	Opt opt= parse_args(argc, argv);
	Ctx ctx(opt);
	Frac target;
	target.set(opt.target, 1);
	unsigned long long count= 0;
	count+= ctx.count_state(0, opt.n, NUM, target);
	count+= ctx.count_state(0, opt.n, SUM, target);
	count+= ctx.count_state(0, opt.n, PROD, target);
	count+= ctx.count_state(0, opt.n, QUOT, target);

	cout << "mode=" << opt.mode << " n=" << opt.n << " target=" << opt.target
			 << " max_abs=" << opt.max_abs << " c_style=" << opt.c_style << "\n";
	cout << "memo_states=" << ctx.memo.size() << "\n";
	cout << "cases_considered=" << ctx.cases_considered << "\n";
	cout << "target_count=" << count << "\n";
	return 0;
}
