#ifndef __HODL_H
#define __HODL_H

#include <stdint.h>
#include <x86intrin.h>

#define AES_ITERATIONS 		15

#define GARBAGE_SIZE		(1 << 30)
#define GARBAGE_CHUNK_SIZE	(1 << 6)
#define GARBAGE_SLICE_SIZE	(1 << 12)
#define TOTAL_CHUNKS		(1 << 24)		// GARBAGE_SIZE / GARBAGE_CHUNK_SIZE
#define COMPARE_SIZE		(1 << 18)		// GARBAGE_SIZE / GARBAGE_SLICE_SIZE

typedef union _CacheEntry
{
	uint32_t dwords[GARBAGE_SLICE_SIZE >> 2] __attribute__((aligned(16)));
	__m128i dqwords[GARBAGE_SLICE_SIZE >> 4] __attribute__((aligned(16)));
} CacheEntry;

int scanhash_hodl(int thr_id, int totalThreads, uint32_t *pdata, const CacheEntry *scratchpad, const uint32_t *ptarget, unsigned long *hashes_done);
void GenRandomGarbage(CacheEntry *Garbage, int totalThreads, uint32_t *pdata, int thr_id);

#endif		// __HODL_H
