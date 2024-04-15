#include <assert.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <unistd.h>

#include "memlib.h"
#include "mm.h"


team_t team = {
    /* Team name */
    "ateam",
    /* First member's full name */
    "Harry Bovik",
    /* First member's email address */
    "bovik@cs.cmu.edu",
    /* Second member's full name (leave blank if none) */
    "",
    /* Second member's email address (leave blank if none) */
    ""};

/* single word (4) or double word (8) alignment */
#define ALIGNMENT 8

/* rounds up to the nearest multiple of ALIGNMENT */
#define ALIGN(size) (((size) + (ALIGNMENT - 1)) & ~0x7)

#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

/* Basic constants and macros */
#define WSIZE 4             // 워드의 크기
#define DSIZE 8             // 더블워드의 크기
#define CHUNKSIZE (1 << 12) // 초기 가용블록과 힙 확장을 위한 기본 크기
#define MAX(x, y) ((x) > (y) ? (x) : (y))

/*블록의 size와 alloc 여부 패킹*/
#define PACK(size, alloc) ((size) | (alloc))

/* Read and write a word at address p */
#define GET(p) (*(unsigned int *)(p))              // p가 참조하는 워드를 읽어서 리턴, p(void *)
#define PUT(p, val) (*(unsigned int *)(p) = (val)) // 인자 p가 가리키는 워드에 val 저장

/* Read the size and allocated fields from address p */
#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 header or footer의 size return
#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 있는 header or footer의 allocated bit return

/* Given block ptr bp ,compute address of its header and footer */
#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 블록의 header를 가리키는 포인터 return
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록의 footer를 가리키는 포인터 return

/* Given block ptr bp,compute address of next and previous blocks */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(((char *)(bp) - WSIZE))) // 다음 블록의 포인터 return
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(((char *)(bp) - DSIZE))) // 이전 블록의 포인터 return

#define MAX_HEAP (20*(1<<20)) 

static char *heap_listp;
static char *prev_bp=NULL;

static void *extend_heap(size_t words);
static void *find_fit(size_t asize);
static void place(char *bp, size_t asize);
static void *coalesce(void *bp);


/*
 * mm_init - initialize the malloc package.
 */
int mm_init(void) {

    // 메모리 시스템에서 4워드를 가져와서 빈 가용 리스트를 만들 수 있도록 초기화
    heap_listp = mem_sbrk(4 * WSIZE);
    if (heap_listp == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                            /*Alignment padding */
    PUT(heap_listp + (1 * WSIZE), PACK(DSIZE, 1)); /* Prologue header */
    PUT(heap_listp + (2 * WSIZE), PACK(DSIZE, 1)); /* Prologue footer */
    PUT(heap_listp + (3 * WSIZE), PACK(0, 1));     /* Epilogue header */
    heap_listp += (2 * WSIZE);                     // prologue의 hedaer와 footer사이(footer시작지점)

    // 힙을 CHUNLSIZE 바이트로 확장, 초기 가용 블록 생성
    if (extend_heap(CHUNKSIZE / WSIZE) == NULL)
        return -1;
    return 0;
}

static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    // size를 2워드 정렬 체계에 맞게 부여(words가 홀수이면 words+1)
    size = words * WSIZE;
    // size 만큼의 공간 할당
    bp = mem_sbrk(size);
    // 공간할당 실패시 NULL return
    if ((long)bp == -1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새 가용블록의 header
    PUT(FTRP(bp), PACK(size, 0));         // 새 가용블록의 footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 힙의 에필로그 header의 위치 재설정(0 byte )

    // 이전의 블럭이 가용블럭이었다면 연결(가용블럭 병합)
    return coalesce(bp);
}

/*
 * mm_malloc - Allocate a block by incrementing the brk pointer.
 *     Always allocate a block whose size is a multiple of the alignment.
 */
void *mm_malloc(size_t size) {
    size_t asize;      // 실제 할당할 메모리 블록의 크기를 저장하기 위한 변수
    size_t extendsize; // 힙을 확장할 때 필요한 블록의 크기를 저장하기 위한 변수
    char *bp;

    if (size == 0)
        return NULL;

    // 요청 size가 블록 최소크기(2워드) 보다 작거나 같으면
    if (size <= DSIZE)
        asize = 2 * DSIZE; // 4워드 할당(header와 footer + 최소 크기의 블록)
    else

        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 오버헤드 바이트 추가 후 인접 8의 배수로 반올림

    // 요청된 size에 맞는 가용블록 찾기
    bp = find_fit(asize);

    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }
    // 새로운 가용 블록 생성을 위한 힙 확장
    extendsize = MAX(asize, CHUNKSIZE);
    bp = extend_heap(extendsize / WSIZE);

    if (bp != NULL) {
        place(bp, asize);
        return bp;
    } else {
        return NULL;
    }
}
// // First Fit 알고리즘을 사용하여 요청된 크기에 맞는 가용 블록을 찾습니다.
// // 만약 적절한 가용 블록을 찾으면 해당 블록의 포인터를 반환하고, 찾지 못하면 NULL을 반환합니다.
// static void *find_fit(size_t asize) {
//     void *bp;

//     // 메모리 블록 리스트를 순회하여 첫 번째로 맞는 가용 블록을 찾습니다.
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             return bp; // 가용 블록을 찾은 경우 해당 블록의 포인터를 반환합니다.
//         }
//     }
//     return NULL; // 적절한 가용 블록을 찾지 못한 경우 NULL을 반환합니다.
// }

/* next fit */
static void *find_fit(size_t asize) {
    void *bp = prev_bp ? prev_bp : heap_listp;
    while (GET_SIZE(HDRP(bp)) > 0) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            prev_bp = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    bp = heap_listp;
    while (GET_SIZE(HDRP(bp)) > 0) {
        if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
            prev_bp = bp;
            return bp;
        }
        bp = NEXT_BLKP(bp);
    }
    return NULL;
}

// // Best Fit 알고리즘을 사용하여 요청된 크기에 맞는 가장 적합한 가용 블록을 찾습니다.
// // 만약 적절한 가용 블록을 찾으면 해당 블록의 포인터를 반환하고, 찾지 못하면 NULL을 반환합니다.
// static void *find_fit(size_t asize) {
//     char *bp;
//     char *best_fit = NULL;
//     size_t min_diff = MAX_HEAP; // 최소 차이를 저장하기 위한 변수

//     // 메모리 블록 리스트를 순회하여 가장 근접한 크기의 가용 블록을 찾습니다.
//     for (bp = heap_listp; GET_SIZE(HDRP(bp)) > 0; bp = NEXT_BLKP(bp)) {
//         if (!GET_ALLOC(HDRP(bp)) && (asize <= GET_SIZE(HDRP(bp)))) {
//             size_t diff = GET_SIZE(HDRP(bp)) - asize;
//             if (diff < min_diff) {
//                 min_diff = diff; // 더 작은 차이를 갖는 가용 블록을 찾습니다.
//                 best_fit = bp;
//             }
//         }
//     }
//     return best_fit; // 가장 근접한 크기의 가용 블록을 반환합니다.
// }

// 가용 블록을 사용하여 요청된 크기의 메모리 블록을 할당하고, 필요한 작업을 수행합니다.
static void place(char *bp, size_t asize) {
    size_t bsize = GET_SIZE(HDRP(bp)); // 가용 블록의 크기

    if ((bsize - asize) >= (2 * DSIZE)) {
        // 가용 블록을 분할하여 요청된 크기의 메모리 블록을 할당하고 남은 부분을 가용 블록으로 설정합니다.
        PUT(HDRP(bp), PACK(asize, 1));         // 할당된 블록의 헤더를 설정합니다.
        PUT(FTRP(bp), PACK(asize, 1));         // 할당된 블록의 푸터를 설정합니다.
        bp = NEXT_BLKP(bp);                    // 다음 블록으로 이동합니다.
        PUT(HDRP(bp), PACK(bsize - asize, 0)); // 남은 가용 블록의 헤더를 설정합니다.
        PUT(FTRP(bp), PACK(bsize - asize, 0)); // 남은 가용 블록의 푸터를 설정합니다.
    } else {
        // 가용 블록을 분할할 만큼의 공간이 없는 경우, 가용 블록 전체를 할당된 블록으로 설정합니다.
        PUT(HDRP(bp), PACK(bsize, 1)); // 가용 블록 전체를 할당된 블록으로 설정합니다.
        PUT(FTRP(bp), PACK(bsize, 1)); // 가용 블록 전체를 할당된 블록으로 설정합니다.
    }
}

/*
 * mm_free - Freeing a block does nothing.
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0)); // 가용블록으로 전환(header 정보 수정=>0)
    PUT(FTRP(bp), PACK(size, 0)); // 가용블록으로 전환(footer 정보 수정=>0)
    coalesce(bp);                 // 이전 블럭이 가용블록이면 병합
}

// 블록을 반환하고 경계 태크 연결을 사용해서 상수 시간에 인접 가용 블록들과 통합
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));
    // case 1 : 이전 블록과 다음 블록이 모두 할당되어 있는 경우
    if (prev_alloc && next_alloc) {
        return bp;
    }
    // case2 : 이전 블록은 할당되어 있고 다음 블록은 가용 상태인 경우
    else if (prev_alloc && !next_alloc) {
        size += GET_SIZE(HDRP(NEXT_BLKP(bp))); // 현재 블록의 크기 증가(+다음블록의 header size)

        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 bp 기준으로 footer 가용블록 설정
        PUT(HDRP(bp), PACK(size, 0));            // 련재 bp 기준으로 header 가용블록 설정

    }
    // case3 : 이전 블록은 가용 상태이고 다음 블록은 할당되어 있는 경우
    else if (!prev_alloc && next_alloc) {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 현재 블록의 크기 증가(+이전블록의 header size)

        PUT(FTRP(bp), PACK(size, 0)); // 현재 bp 기준으로 footer 가용블록 설정
        bp = PREV_BLKP(bp);           // 현재 bp를 이전 블록으로 변환
        PUT(HDRP(bp), PACK(size, 0)); // 현재 bp(이전 블록) 기준으로 header 가용블록 설정

    }
    // case4 : 이전 블록과 다음 블록이 모두 가용 상태인 경우
    else {
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 현재 블록의 크기 증가(+이전블록의 header size,다음블록의 header size)

        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 bp 기준으로 footer 가용블록 설정
        bp = PREV_BLKP(bp);                      // 현재 bp를 이전 블록으로 변환
        PUT(HDRP(bp), PACK(size, 0));            // 현재 bp(이전 블록) 기준으로 header 가용블록 설정
    }
    prev_bp=bp;
    return bp;
}

/*
 * mm_realloc - Implemented simply in terms of mm_malloc and mm_free
 */
void *mm_realloc(void *bp, size_t size) {
    if (size <= 0) {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL) {
        return mm_malloc(size);
    }
    void *newp = mm_malloc(size);
    if (newp == NULL) {
        return 0;
    }
    size_t oldsize = GET_SIZE(HDRP(bp));
    if (size < oldsize) {
        oldsize = size;
    }
    memcpy(newp, bp, oldsize);
    mm_free(bp);
    return newp;
}
