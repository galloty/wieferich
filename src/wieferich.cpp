/*
Copyright 2020, Yves Gallot

wieferich is free source code, under the MIT license (see LICENSE). You can redistribute, use and/or modify it.
Please give feedback to the authors if improvement is realized. It is distributed in the hope that it will be useful.
*/

// #define TEST	true

#include <cstdint>
#define _USE_MATH_DEFINES
#include <cmath>
#include <iostream>
#include <queue>
#include <thread>
#include <mutex>
#include <chrono>

#ifdef TEST
#include <gmp.h>

inline void mpz_set_ui_64(mpz_t & rop, const uint64_t n)
{
	mp_limb_t * const p_limb = mpz_limbs_write(rop, 1);
	p_limb[0] = n;
	mpz_limbs_finish(rop, 1);
}

inline void mpz_get_ui_128(const mpz_t & rop, __uint128_t & n)
{
	const size_t size = mpz_size(rop);
	n = 0;
	const mp_limb_t * const 
	p_limb = mpz_limbs_read(rop);
	if (size >= 1) n |= p_limb[0];
	if (size >= 2) n |= (__uint128_t(p_limb[1]) << 64);
}
#endif

inline int log2_64(const uint64_t x) { return 63 - __builtin_clzll(x); }

typedef uint64_t vec4_uint64_t[4] __attribute__((aligned(32)));

inline void vec4_set(vec4_uint64_t y, const vec4_uint64_t x) { for (size_t i = 0; i < 4; ++i) y[i] = x[i]; }

// 2^64 * u - p * p_inv = 1, binary extended GCD
inline uint64_t invert(const uint64_t p)
{
	const uint64_t a_2 = uint64_t(1) << 63, b = p;
	uint64_t g1 = a_2, g2 = b, t = a_2, s = (1 + b) / 2;
	while (g1 != 1)
	{
		if (g1 > g2)
		{
			g1 /= 2;
			t /= 2;
			if (s % 2 != 0)
			{
				s += b;
				t += a_2;
			}
			s /= 2;
		}
		else g2 -= g1;
	}
	return -t;
}

struct M2p { uint64_t l, h; };

// Peter L. Montgomery, Modular multiplication without trial division, Math. Comp.44 (1985), 519–521.
class M2pArith : public M2p
{
private:
	const uint64_t _p, _q;

private:
	inline static uint64_t sub_mod(uint64_t & z, const uint64_t x, const uint64_t y, const uint64_t p)
	{
		const uint64_t mask_c = (y > x) ? uint64_t(-1) : 0;
		z = x - y + (p & mask_c);
		return -mask_c;
	}

public:
	M2pArith(const uint64_t p) : _p(p), _q(invert(p))
	{
		// 2^64 mod p^2 is (2^64, p^2) residue of 1
		if (p < (uint64_t(1) << 32))
		{
			// r_p2 = 2^64 mod p^2
			const uint64_t p2 = p * p;
			const int s = 63 - log2_64(p2);
			uint64_t m = p2 << s, r_p2 = -m;
			for (int i = 0; i < s; ++i) { m >>= 1; if (r_p2 >= m) r_p2 -= m; }
			this->l = r_p2 % p; this->h = r_p2 / p;
		}
		else
		{
			// 2^64 mod p^2 = 2^64 then compute 2^64 mod p
			const uint64_t mp = -p;
			this->l = mp % p; this->h = mp / p + 1;
		}
	}

	virtual ~M2pArith() {}

	void set(const uint64_t l, const uint64_t h) { this->l = l; this->h = h; }

	// duplicate if b is true
	void dup_cond(const bool b)
	{
		const uint64_t l1 = this->l, h1 = this->h, p = this->_p;
		const uint64_t mask_b = b ? uint64_t(-1) : 0, l2 = l1 & mask_b, h2 = h1 & mask_b;

		const uint64_t mask_c = (l1 >= p - l2) ? uint64_t(-1) : 0;
		const uint64_t sl = l1 + l2;
		this->l = sl - (p & mask_c);

		const uint64_t xh = h1 + (1 & mask_c);		// 0 <= xh <= p
		const uint64_t sh = xh + h2;				// 0 <= sh < 2p
		const uint64_t mask_c2 = (xh >= p - h2) ? uint64_t(-1) : 0;
		this->h = sh - (p & mask_c2);				// 0 <= h < p
	}

	void dup() { dup_cond(true); }

	// Dorais, F. G.; Klyve, D., "A Wieferich Prime Search Up to 6.7x10^15", Journal of Integer Sequences. 14 (9), 2011.
	void square()
	{
		const uint64_t l = this->l, h = this->h, p = this->_p, q = this->_q;

		const __uint128_t t = l * __uint128_t(l);
		const uint64_t u0 = q * uint64_t(t);
		const uint64_t t1 = uint64_t(t >> 64);
		const uint64_t v1 = uint64_t((p * __uint128_t(u0)) >> 64);

		const __uint128_t xlh = l * __uint128_t(h);
		const __uint128_t xlhu = xlh + u0;
		const __uint128_t tp = xlhu + xlh;
		// 0 <= tp_h < 2p. tp_h >= p if tp_h >= 2^64 or tp_h >= p
		const uint64_t tp_h = uint64_t(tp >> 64), mask_tpc = ((tp < xlh) | (tp_h >= p)) ? uint64_t(-1) : 0;
		const uint64_t up0 = q * uint64_t(tp);
		const uint64_t t1p = tp_h - (mask_tpc & p);	// 0 <= t1p < p
		const uint64_t v1p = uint64_t((p * __uint128_t(up0)) >> 64);

		// 0 <= t1, v1 < p, 0 <= t1p, v1p < p
		uint64_t z0, z1;
		const uint64_t c = sub_mod(z0, t1, v1, p);
		sub_mod(z1, t1p, v1p, p);
		sub_mod(z1, z1, c, p);

		this->l = z0; this->h = uint64_t(z1);
	}

	// To convert a residue to an integer, apply Algorithm REDC
	M2p get() const
	{
		const uint64_t l = this->l, h = this->h, p = this->_p, q = this->_q;

		const uint64_t u0 = q * l;
		const uint64_t v1 = uint64_t((p * __uint128_t(u0)) >> 64);

		const __uint128_t tp = h + __uint128_t(u0);
		const uint64_t up0 = q * uint64_t(tp);
		const uint64_t t1p = uint64_t(tp >> 64);
		const uint64_t v1p = uint64_t((p * __uint128_t(up0)) >> 64);

		uint64_t z0, z1;
		const uint64_t c = sub_mod(z0, 0, v1, p);
		sub_mod(z1, t1p, v1p, p);
		sub_mod(z1, z1, c, p);

		M2p r; r.l = z0; r.h = uint64_t(z1);
		return r;
	}
};

// 2^n mod p^2
inline M2p two_pow_mod2(const uint64_t n, const uint64_t p)
{
	M2pArith x(p);	// x = 1
	x.dup();		// x = 2
	for (uint64_t b = (uint64_t(1) << (log2_64(n) - 1)); b != 0; b >>= 1)
	{
		x.square();
		x.dup_cond((n & b) != 0);
	}
	return x.get();
}

inline void check(const vec4_uint64_t & p, vec4_uint64_t & l, vec4_uint64_t & h)
{
	bool parallel = true;

	vec4_uint64_t n;
	for (size_t j = 0; j < 4; ++j)
	{
		if (p[j] == 0) parallel = false;
		n[j] = p[j] - 1;
	}

	const int lg = log2_64(n[0]);
	for (size_t j = 1; j < 4; ++j) if (log2_64(n[j]) != lg) parallel = false;

	if (parallel)
	{
		M2pArith x0(p[0]), x1(p[1]), x2(p[2]), x3(p[3]);
		x0.dup(); x1.dup(); x2.dup(); x3.dup();

		for (uint64_t b = (uint64_t(1) << (lg - 1)); b != 0; b >>= 1)
		{
			x0.square(); x0.dup_cond((n[0] & b) != 0);
			x1.square(); x1.dup_cond((n[1] & b) != 0);
			x2.square(); x2.dup_cond((n[2] & b) != 0);
			x3.square(); x3.dup_cond((n[3] & b) != 0);
		}

		M2p r[4]; r[0] = x0.get(), r[1] = x1.get(), r[2] = x2.get(), r[3] = x3.get();
		for (size_t j = 0; j < 4; ++j) { l[j] = r[j].l; h[j] = r[j].h; }
	}
	else
	{
		for (size_t j = 0; j < 4; ++j)
		{
			const uint64_t pj = p[j];
			if (pj == 0) continue;
			const M2p r = two_pow_mod2(n[j], pj);
			l[j] = r.l; h[j] = r.h;
		}
	}

#ifdef TEST
	mpz_t zp2, zn, two, zr; mpz_inits(zp2, zn, two, zr, nullptr);
	mpz_set_ui(two, 2);
	for (size_t j = 0; j < 4; ++j)
	{
		const uint64_t pj = p[j];
		if (pj == 0) continue;
		mpz_set_ui_64(zp2, pj); mpz_set_ui_64(zn, n[j]); mpz_mul(zp2, zp2, zp2);
		mpz_powm(zr, two, zn, zp2);
		__uint128_t r; mpz_get_ui_128(zr, r);
		if ((l[j] != uint64_t(r % pj)) | (h[j] != uint64_t(r / pj)))
		{
			std::cerr << "Error: p = " << pj << std::endl;
		}
	}
	mpz_clears(zp2, zn, two, zr, nullptr);
#endif
}

class Wieferich
{
private:
	static const size_t p_size = 256;

	struct PArray
	{
		vec4_uint64_t data[p_size];	// 8 KB

		void get(const size_t i, vec4_uint64_t p) { vec4_set(p, data[i]); }
	};

	class PArrayFiller
	{
	private:
		PArray & _p_array;
		size_t _iv = 0, _ia = 0;
		vec4_uint64_t _v;

	public:
		PArrayFiller(PArray & p_array) : _p_array(p_array) {}
		virtual ~PArrayFiller() {};

		bool add(const uint64_t p)
		{
			_v[_iv] = p;
			_iv = (_iv + 1) % 4;
			if (_iv == 0)
			{
				vec4_set(_p_array.data[_ia], _v);
				_ia = (_ia + 1) % p_size;
				return (_ia == 0);
			}
			return false;
		}
	};

private:
	const uint32_t _p_min, _p_max;

	static const size_t max_queue_size = 1024;

	std::mutex _p_queue_mutex;
	std::queue<PArray> _p_queue;

private:
	void prime_gen()
	{
		static const uint32_t sp_max = 1 << 16;
		static const size_t sieve_size = sp_max / 2;	// sieve with an odd prime table.
		static const size_t odd_prime_count = 6541;		// # odd primes with p < 2^16.

		bool sieve[sieve_size];
		uint32_t prm[odd_prime_count];
		uint32_t prm_ptr[odd_prime_count];

		prm[0] = 3; prm[1] = 5; prm[2] = 7;
		uint32_t i = 3;
		for (uint32_t k = 11; k < sp_max; k += 2)
		{
			const uint32_t s = uint32_t(std::sqrt(double(k))) + 1;
			uint32_t d; for (d = 3; d <= s; d += 2) if (k % d == 0) break;
			if (d > s) prm[i++] = k;
		}

		// if (i != odd_prime_count) throw;

		for (size_t k = 0; k < sieve_size; ++k) sieve[k] = false;

		const uint64_t p0 = ((1000000000000ull * _p_min) / sp_max) * sp_max;
		const uint64_t p1 = (_p_max < 18446745) ? ((1000000000000ull * _p_max) / sp_max + 1) * sp_max : uint64_t(-1);
		std::cout << "p in [" << p0 << "; " << p1 << "] " << std::endl;

		if (_p_min == 0)
		{
			sieve[0] = true;	// p = 1
			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				const size_t p = prm[i];
				bool first = true;
				size_t k = (p - 1) / 2;
				for (; k < sieve_size; k += p) if (first) first = false; else sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}
		}
		else
		{
			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				const size_t p = prm[i];
				size_t o = p - size_t(p0 % p); if (o % 2 == 0) o += p;
				size_t k = (o - 1) / 2;
				for (; k < sieve_size; k += p) sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}
		}

		PArray p_array;
		PArrayFiller filler(p_array);
		size_t queue_size = 0;

		for (uint64_t jp = p0; true; jp += sp_max)
		{
			for (size_t kp = 0; kp < sieve_size; ++kp)
			{
				if (!sieve[kp])
				{
					const uint64_t p = jp + 2 * kp + 1;
					if (filler.add(p))
					{
						std::lock_guard<std::mutex> guard(_p_queue_mutex);
						_p_queue.push(p_array);
						queue_size = _p_queue.size();
						if (p >= p1)
						{
							while (!filler.add(0));
							_p_queue.push(p_array);
							return;
						}
					}
				}
			}

			for (size_t k = 0; k < sieve_size; ++k) sieve[k] = false;

			for (size_t i = 0; i < odd_prime_count; ++i)
			{
				size_t k = prm_ptr[i], p = prm[i];
				for (; k < sieve_size; k += p) sieve[k] = true;
				prm_ptr[i] = uint32_t(k - sieve_size);
			}

			while (queue_size > max_queue_size)
			{
				// std::cout << "prime_gen: waiting... p ~ " << jp + 1 << std::endl;
				std::this_thread::sleep_for(std::chrono::milliseconds(100));
				std::lock_guard<std::mutex> guard(_p_queue_mutex);
				queue_size = _p_queue.size();
			}
		}
	}

public:
	Wieferich(const uint32_t p_min, const uint32_t p_max) : _p_min(p_min), _p_max(p_max)
	{
		std::thread t_gen_p([=] { prime_gen(); }); t_gen_p.detach();

		PArray p_array;

		int64_t A_min = uint64_t(-1) / 2;
		auto t0 = std::chrono::steady_clock::now();
		uint64_t p0 = 0;

		while (true)
		{
			bool found = false;
			{
				std::lock_guard<std::mutex> guard(_p_queue_mutex);
				if (!_p_queue.empty())
				{
					found = true;
					p_array = _p_queue.front();
					_p_queue.pop();
				}
			}

			if (!found)
			{
				// std::cout << "Waiting input..." << std::endl;
				std::this_thread::sleep_for(std::chrono::milliseconds(10));
			}
			else
			{
				for (size_t i = 0; i < p_size; ++i)
				{
					vec4_uint64_t p; p_array.get(i, p);
					vec4_uint64_t l, h; check(p, l, h);
					for (size_t j = 0; j < 4; ++j)
					{
						const uint64_t pj = p[j], lj = l[j], hj = h[j];
						if (pj == 0) return;
						if (lj == 1)
						{
							const int64_t a = (hj > pj / 2) ? hj - pj : hj, A = std::abs(a);
							if (A <= A_min)
							{
								const char sign = (A == a) ? '+' : '-';
								std::cout << pj << ": 1 " << sign << " " << A << " p" << "                 " << std::endl;
								A_min = std::max(A, int64_t(10));
							}
						}
					}
				}

				vec4_uint64_t p; p_array.get(p_size - 1, p);
				const uint64_t p1 = p[3];

				const auto t1 = std::chrono::steady_clock::now();
				const std::chrono::duration<double> dt = t1 - t0;
				if (dt.count() > 5)
				{
					if (p0 != 0)
					{
						const double sec_T = dt.count() * 1e12 / (p1 - p0);
						std::cout << p1 << ", " << int(sec_T) << " sec/T\r";
					}
					t0 = t1; p0 = p1;
				}
			}
		}
	}

	virtual ~Wieferich() {}
};

int main(int argc, char * argv[])
{
	std::cerr << "wieferich: search for Wieferich primes" << std::endl;
	std::cerr << " Copyright (c) 2020, Yves Gallot" << std::endl;
	std::cerr << " wieferich is free source code, under the MIT license." << std::endl << std::endl;
	std::cerr << " Usage: wieferich <p_min> <p_max>" << std::endl;
	std::cerr << "   p_min: the start of the p range, in T (10^12) values (default 0)" << std::endl;
	std::cerr << "   p_max: the end of the p range, in T (10^12) values (default p_min + 1)" << std::endl;

	const uint32_t p_min = (argc > 1) ? std::min(std::atoi(argv[1]), 18446744) : 0;
	const uint32_t p_max = (argc > 2) ? std::min(std::atoi(argv[2]), 18446745) : p_min + 1;

	Wieferich(p_min, p_max);

	return EXIT_SUCCESS;
}
