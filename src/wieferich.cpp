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
#include <fstream>
#include <sstream>
#include <queue>
#include <thread>
#include <mutex>
#include <atomic>
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

#define		TERA	1000000000000ull

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
	// p * p_inv = 1 (mod 2^64) (Newton's method)
	constexpr static uint64_t invert(const uint64_t p)
	{
		uint64_t p_inv = 1, prev = 0;
		while (p_inv != prev) { prev = p_inv; p_inv *= 2 - p * p_inv; }
		return p_inv;
	}

public:
	M2pArith(const uint64_t p) : _p(p), _q(invert(p))
	{
		// 2^64 mod p^2 is (2^64, p^2) residue of 1
		if ((p >> 32) == 0)
		{
			const uint64_t p2 = p * p, r_p2 = (-p2) % p2;	// 2^64 mod p^2
			this->l = r_p2 % p; this->h = r_p2 / p;
		}
		else
		{
			// 2^64 mod p^2 = 2^64
			const uint64_t mp = -p;	// 2^64 - p
			this->l = mp % p; this->h = mp / p + 1;
		}
	}

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
		sub_mod(z1, t1p, v1p + c, p);

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
		sub_mod(z1, t1p, v1p + c, p);

		M2p r; r.l = z0; r.h = uint64_t(z1);
		return r;
	}
};

class Wieferich
{
private:
	static const size_t p_size = 1024;

	struct PArray
	{
		uint64_t data[p_size];	// 8 KB
	};

private:
	const uint32_t _p_min, _p_max;

	static const size_t max_queue_size = 1024;

	std::mutex _p_queue_mutex;
	std::queue<PArray> _p_queue;
	bool _end_range = false;
	std::atomic<size_t> _running_threads = 0;

	std::mutex _output_mutex;
	std::atomic<uint64_t> _A_min = uint64_t(-1) / 2;
	std::atomic<uint64_t> _p_cur = 0;

private:
	static uint64_t addMp(const uint64_t a, const uint64_t b, const uint64_t p)
	{
		const uint64_t c = (a >= p - b) ? p : 0;
		return a + b - c;
	}

	static uint64_t mulMp(const uint64_t a, const uint64_t b, const uint64_t p, const uint64_t  q)
	{
		const __uint128_t t = a * __uint128_t(b);
		const uint64_t ab_l = uint64_t(t), ab_h = uint64_t(t >> 64);
		const uint64_t m = ab_l * q, mp = uint64_t((m * __uint128_t(p)) >> 64);
		const uint64_t r = ab_h - mp;
		return (ab_h < mp) ? r + p : r;
	}

	static bool strong_prp(const uint64_t p)
	{
		const uint64_t pmo = p - 1;
		const int t = 63 - __builtin_clzll(pmo & -pmo);	// this is ctz, p = d*2^t + 1, where d is odd
		const uint64_t exp = p >> t;
		uint64_t curBit = 0x8000000000000000 >> (__builtin_clzll(exp) + 1);

		const uint64_t q = M2pArith::invert(p);
		const uint64_t one = (-p) % p;
	
		uint64_t a = addMp(one, one, p);

 		while (curBit != 0)
		{
			a = mulMp(a, a, p, q);
			if ((exp & curBit) != 0) a = addMp(a, a, p);
			curBit >>= 1;
		}

		// a^d = 1 (mod p) or a^{d*2^0} = -1 (mod p)
		if ((a == one) | (a == p - one)) return true;

		// a^{d*2^s} = -1 (mod p) for some s in 0 < s < t
		for (int s = 1; s < t; ++s)
		{
			a = mulMp(a, a, p, q);
			if (a == p - one) return true;
		}

		return false;
	}

private:
	void pseudo_prime_gen()
	{
		// Segmented sieve of Eratosthenes: outputs have no factor < 65537.
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

		const uint64_t p0 = ((TERA * _p_min) / sp_max) * sp_max;
		const uint64_t p1 = (_p_max < 18446745) ? ((TERA * _p_max) / sp_max + 1) * sp_max : uint64_t(-1);
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
		size_t p_array_i = 0;
		size_t queue_size = 0;

		for (uint64_t jp = p0; true; jp += sp_max)
		{
			for (size_t kp = 0; kp < sieve_size; ++kp)
			{
				if (!sieve[kp])
				{
					const uint64_t p = jp + 2 * kp + 1;
					// if (strong_prp(p))
					{
						p_array.data[p_array_i] = p;
						p_array_i = (p_array_i + 1) % p_size;
						if (p_array_i == 0)
						{
							std::lock_guard<std::mutex> guard(_p_queue_mutex);
							_p_queue.push(p_array);
							queue_size = _p_queue.size();
							if (p >= p1)
							{
								_end_range = true;
								return;
							}
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
				std::this_thread::sleep_for(std::chrono::milliseconds(100));
				std::lock_guard<std::mutex> guard(_p_queue_mutex);
				queue_size = _p_queue.size();
			}
		}
	}

	constexpr static int log2_64(const uint64_t x) { return 63 - __builtin_clzll(x); }

	static void check(const uint64_t p[4], uint64_t l[4], uint64_t h[4])
	{
		uint64_t n[4]; for (size_t j = 0; j < 4; ++j) n[j] = p[j] - 1;

		bool parallel = true;
		const int lg = log2_64(n[0]);
		for (size_t j = 1; j < 4; ++j) if (log2_64(n[j]) != lg) parallel = false;

		// 2^n mod p^2
		if (parallel)
		{
			M2pArith x0(p[0]), x1(p[1]), x2(p[2]), x3(p[3]);	// x = 1
			x0.dup(); x1.dup(); x2.dup(); x3.dup();				// x = 2

			uint64_t b = uint64_t(1) << (lg - 1);
			x0.dup(); x1.dup(); x2.dup(); x3.dup();				// first step: 2^2 = 2 + 2
			x0.dup_cond((n[0] & b) != 0); x1.dup_cond((n[1] & b) != 0); x2.dup_cond((n[2] & b) != 0); x3.dup_cond((n[3] & b) != 0);

			for (b >>= 1; b != 0; b >>= 1)
			{
				x0.square(); x1.square(); x2.square(); x3.square();
				x0.dup_cond((n[0] & b) != 0); x1.dup_cond((n[1] & b) != 0); x2.dup_cond((n[2] & b) != 0); x3.dup_cond((n[3] & b) != 0);
			}

			M2p r[4]; r[0] = x0.get(), r[1] = x1.get(), r[2] = x2.get(), r[3] = x3.get();
			for (size_t j = 0; j < 4; ++j) { l[j] = r[j].l; h[j] = r[j].h; }
		}
		else
		{
			for (size_t j = 0; j < 4; ++j)
			{
				M2pArith x(p[j]);	// x = 1
				x.dup();			// x = 2

				uint64_t b = uint64_t(1) << (log2_64(n[j]) - 1);
				x.dup(); x.dup_cond((n[j] & b) != 0);	// first step: 2^2 = 2 + 2

				for (b >>= 1; b != 0; b >>= 1)
				{
					x.square();
					x.dup_cond((n[j] & b) != 0);
				}
				const M2p r = x.get();
				l[j] = r.l; h[j] = r.h;
			}
		}

#ifdef TEST
		mpz_t zp2, zn, two, zr; mpz_inits(zp2, zn, two, zr, nullptr);
		mpz_set_ui(two, 2);
		for (size_t j = 0; j < 4; ++j)
		{
			const uint64_t pj = p[j];
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

	void output(const uint64_t p, const int64_t a)
	{
		const char sign = (a < 0) ? '-' : '+';
		std::stringstream ss; ss << p << ": 1 " << sign << " " << std::abs(a) << " p";
		std::lock_guard<std::mutex> guard(_output_mutex);
		std::cout << ss.str() << "                             " << std::endl;
		std::ofstream logFile("wieferich.log", std::ios::app);
		if (logFile.is_open())
		{
			logFile << ss.str() << std::endl;
			logFile.flush(); logFile.close();
		}
	}

	void test_prime()
	{
		PArray p_array;

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
				if (_end_range) { _running_threads--; return; }
				// std::cout << "Waiting input..." << std::endl;
				std::this_thread::sleep_for(std::chrono::milliseconds(10));
			}
			else
			{
				for (size_t i = 0; i < p_size; i += 4)
				{
					const uint64_t * const p = &p_array.data[i];
					uint64_t l[4], h[4]; check(p, l, h);
					for (size_t j = 0; j < 4; ++j)
					{
						if (l[j] == 1)
						{
							const uint64_t pj = p[j], hj = h[j];
							const int64_t a = (hj > pj / 2) ? hj - pj : hj;
							const uint64_t A = std::abs(a);
							if (A <= _A_min)
							{
								output(pj, a);
								_A_min = std::max(A, uint64_t(10));
							}
						}
					}
				}
				uint64_t p = p_array.data[p_size - 1];
				_p_cur = std::max(uint64_t(_p_cur), p);
			}
		}
	}

public:
	Wieferich(const uint32_t p_min, const uint32_t p_max, const size_t thread_count) : _p_min(p_min), _p_max(p_max)
	{
		std::thread t_gen_p([=] { pseudo_prime_gen(); }); t_gen_p.detach();
		std::this_thread::sleep_for(std::chrono::milliseconds(100));
		for (size_t i = 0; i < thread_count; ++i)
		{
			_running_threads++;
			std::thread t_test_p([=] { test_prime(); }); t_test_p.detach();
		}

		const uint64_t p2 = (_p_max < 18446745) ? TERA * _p_max : uint64_t(-1);
		auto t0 = std::chrono::steady_clock::now();
		uint64_t p0 = 0;

		while (_running_threads != 0)
		{
			std::this_thread::sleep_for(std::chrono::seconds(5));
			const uint64_t p1 = _p_cur;
			const auto t1 = std::chrono::steady_clock::now();
			const std::chrono::duration<double> dt = t1 - t0;
			if (p0 != 0)
			{
				const double speed = (p1 - p0) / dt.count();
				const double eta = (p2 - p1) / speed;
				std::lock_guard<std::mutex> guard(_output_mutex);
				std::cout << "p = " << p1 << ", dp = " << int(speed * 1e-6) << "M/sec, ETA = " << int(eta / 60.0) << " min      \r";
			}
			t0 = t1; p0 = p1;
		}
	}

	virtual ~Wieferich() {}
};

int main(int argc, char * argv[])
{
	std::cerr << "wieferich: search for Wieferich primes" << std::endl;
	std::cerr << " Copyright (c) 2020, Yves Gallot" << std::endl;
	std::cerr << " wieferich is free source code, under the MIT license." << std::endl << std::endl;
	std::cerr << " Usage: wieferich <n_threads> <p_min> <p_max>" << std::endl;
	std::cerr << "   n_threads: the number of threads (default 3)" << std::endl;
	std::cerr << "   p_min: the start of the p range, in Tera (10^12) values (default 0)" << std::endl;
	std::cerr << "   p_max: the end of the p range, in Tera (10^12) values (default p_min + 1)" << std::endl;

	const size_t n_threads = (argc > 1) ? std::atoi(argv[1]) : 3;
	const uint32_t p_min = (argc > 2) ? std::min(std::atoi(argv[2]), 18446744) : 0;
	const uint32_t p_max = (argc > 3) ? std::min(std::atoi(argv[3]), 18446745) : p_min + 1;

	Wieferich(p_min, p_max, n_threads);

	return EXIT_SUCCESS;
}
