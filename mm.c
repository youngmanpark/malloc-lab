#include "mm.h"
#include "memlib.h"
#include <assert.h>
#include <errno.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/mman.h>
#include <unistd.h>

team_t team = {
    "team_5",
    "Park yeongmin ",
    " py980627@gmail.com",
    "", ""};

/* 8(2워드)의 배수에 맞게 반올림  */
#define ALIGN(size) (((size) + (DSIZE - 1)) & ~0x7)
#define SIZE_T_SIZE (ALIGN(sizeof(size_t)))

#define WSIZE 4             // 워드의 크기
#define DSIZE 8             // 더블워드의 크기
#define CHUNKSIZE (1 << 12) // 초기 가용블록과 힙 확장을 위한 기본 크기 (4096 Byte)
#define LISTLIMIT 12        // 클래스의 최대 개수

/*블록의 size와 alloc 여부 패킹*/
#define PACK(size, alloc) ((size) | (alloc))

/* p가 참조하는 워드 읽고 쓰기 */
#define GET(p) (*(unsigned int *)(p))              // p가 참조하는 워드를 읽어서 리턴, p(void *)
#define PUT(p, val) (GET(p) = (unsigned int)(val)) // 인자 p가 가리키는 워드에 val 저장

/* 블록의 size와 alloc 여부 확인  */
#define GET_SIZE(p) (GET(p) & ~0x7) // 주소 p에 있는 header or footer의 size return
#define GET_ALLOC(p) (GET(p) & 0x1) // 주소 p에 있는 header or footer의 allocated bit return

/* 블록포인터(bp)가 가리키는 header와 footer의 포인터 return */
#define HDRP(bp) ((char *)(bp) - WSIZE)                      // 블록의 header를 가리키는 포인터 return
#define FTRP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)) - DSIZE) // 블록의 footer를 가리키는 포인터 return

/* 블록포인터(bp)의 다음 or 이전 블록 포인터 return */
#define NEXT_BLKP(bp) ((char *)(bp) + GET_SIZE(HDRP(bp)))         // 다음 블록의 포인터 return
#define PREV_BLKP(bp) ((char *)(bp) - GET_SIZE(HDRP(bp) - WSIZE)) // 이전 블록의 포인터 return

/* 블록포인터(bp)의 다음 or 이전 가용블록 포인터 return */
#define PRED_FREEP(bp) (*(void **)(bp))
#define SUCC_FREEP(bp) (*(void **)(bp + WSIZE))

/*클래스의 root*/
#define GET_ROOT(class_n) (*(void **)((char *)(class_listp) + (WSIZE * class_n)))

/*구현 함수*/
static void *extend_heap(size_t words);    // 부족한 힙 공간을 확장
static void *find_fit(size_t asize);       // 할당할 블록크기가 가용리스트에 있는지 탐색
static void place(void *bp, size_t asize); // 할당할 블록의 크기와 맞는 블록이 있으면 (find_fit 진행 후) 배치
static void *coalesce(void *bp);           // 가용블록들을 하나의 블록으로 병합
void putFreeBlock(void *bp);               // 가용리스트에 가용블록 삽입
void removeBlock(void *bp);                // 가용리스트에서 할당된 블록 제거
int get_class(size_t size);                // 요청한 size가 해당되는 클래스 인덱스

/*전역 변수*/
static char *heap_listp;         // 힙의 시작 포인트
static char *class_listp = NULL; // 클래스리스트의 시작 포인트

/*----------------------------------------------mm_function()-----------------------------------------------------------*/

/*
 * mm_init - 할당기 초기화
 */
int mm_init(void) {

    // 메모리 시스템에서 segregated_list+4워드를 가져와서 초기화
    heap_listp = mem_sbrk((LISTLIMIT + 4) * WSIZE);
    if (heap_listp == (void *)-1)
        return -1;

    PUT(heap_listp, 0);                                              // 패딩
    PUT(heap_listp + (1 * WSIZE), PACK((LISTLIMIT + 2) * WSIZE, 1)); // 프롤로그 header
    // segregated_list_class
    for (int i = 2; i < LISTLIMIT + 2; i++)
        PUT(heap_listp + (i * WSIZE), NULL);
    PUT(heap_listp + ((LISTLIMIT + 2) * WSIZE), PACK((LISTLIMIT + 2) * WSIZE, 1)); // 프롤로그 footer
    PUT(heap_listp + ((LISTLIMIT + 3) * WSIZE), PACK(0, 1));                       // 에필로그 header

    class_listp = heap_listp + DSIZE; // 클래스 리스트의 시작 포인트

    return 0;
}

/*
 * mm_malloc - 요청한 size만큼 메모리 할당.
 */
void *mm_malloc(size_t size) {
    size_t asize; // 실제 할당할 메모리 블록의 크기
    void *bp;

    if (size == 0)
        return NULL;

    // 요청 size가 블록 최소크기(4워드) 보다 작거나 같으면
    if (size <= DSIZE)
        asize = 2 * DSIZE; // 4워드 할당(16 byte)
    else
        asize = DSIZE * ((size + (DSIZE) + (DSIZE - 1)) / DSIZE); // 오버헤드 바이트 추가 후 인접 8의 배수로 반올림

    // 요청된 size에 맞는 가용블록 찾기
    bp = find_fit(asize);
    // 가용블록이 있을 경우
    if (bp != NULL) {
        place(bp, asize);
        return bp;
    }

    // 가용블럭이 없을 경우
    bp = extend_heap(asize / WSIZE); // 요청한 size만큼 메모리 할당
    if (bp != NULL) {
        place(bp, asize);
        return bp;
    } else {
        return NULL;
    }
}

/*
 * mm_free - 가용블록으로 전환
 */
void mm_free(void *bp) {
    size_t size = GET_SIZE(HDRP(bp));

    PUT(HDRP(bp), PACK(size, 0)); // 가용블록으로 전환(header 정보 수정=>0)
    PUT(FTRP(bp), PACK(size, 0)); // 가용블록으로 전환(footer 정보 수정=>0)
    coalesce(bp);                 // 인접 블록이 가용블록이면 병합
}

/*
 * mm_realloc -메모리 블록의 크기를 조정하는 데 사용
 */
void *mm_realloc(void *bp, size_t size) {
    if (size <= 0) {
        mm_free(bp);
        return 0;
    }
    if (bp == NULL)
        return mm_malloc(size);

    size_t old_size = GET_SIZE(HDRP(bp));
    size_t next_size = GET_SIZE(HDRP(NEXT_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));

    if (size + 2 * WSIZE <= old_size)
        return bp;
    if (!next_alloc && size + 2 * WSIZE <= old_size + next_size) {
        removeBlock(NEXT_BLKP(bp));
        PUT(HDRP(bp), PACK(old_size + next_size, 1));
        PUT(FTRP(bp), PACK(old_size + next_size, 1));
        return bp;
    }

    void *newp = mm_malloc(size);
    if (newp == NULL)
        return 0;
    memcpy(newp, bp, old_size);
    mm_free(bp);
    return newp;
}

/*----------------------------------------------add_function()-----------------------------------------------------------*/

/*
 * extend_heap - 부족한 힙 공간을 확장
 */
static void *extend_heap(size_t words) {
    char *bp;
    size_t size;

    //
    size = words * WSIZE;
    // size 만큼의 공간 할당
    bp = mem_sbrk(size);
    // 공간할당 실패시 NULL return
    if (bp == (void *)-1)
        return NULL;

    PUT(HDRP(bp), PACK(size, 0));         // 새 가용블록의 header
    PUT(FTRP(bp), PACK(size, 0));         // 새 가용블록의 footer
    PUT(HDRP(NEXT_BLKP(bp)), PACK(0, 1)); // 힙의 에필로그 header의 위치 재설정(0 byte)

    // 이전의 블럭이 가용블럭이었다면 연결(가용블럭 병합)
    return coalesce(bp);
}

/*
 * find_fit - 요청한 size에 대한 가용블록 찾기
 */
static void *find_fit(size_t asize) {
    int class_idx; // 요청된 size가 segregated_list의 어떤 class에 할당할지 찾기
    void *bp;

    for (class_idx = get_class(asize); class_idx < LISTLIMIT; class_idx++) {
        for (bp = GET_ROOT(class_idx); bp != NULL; bp = SUCC_FREEP(bp)) {
            if (GET_SIZE(HDRP(bp)) >= asize) {
                return bp;
            }
        }
    }
    return NULL;
}

/*
 * place - 요청한 size를 할당할 수 있는 블록에 배치
 */
static void place(void *bp, size_t asize) {
    size_t bsize = GET_SIZE(HDRP(bp)); // 가용 블록의 크기

    removeBlock(bp); // 할당될 블록이니 가용리스트 내부에서 제거

    if ((bsize - asize) >= (2 * DSIZE)) {
        // 가용 블록을 분할하여 요청된 크기의 메모리 블록을 할당하고 남은 부분을 가용 블록으로 설정합니다.
        PUT(HDRP(bp), PACK(asize, 1));         // 할당된 블록의 header 설정
        PUT(FTRP(bp), PACK(asize, 1));         // 할당된 블록의 footer 설정
        bp = NEXT_BLKP(bp);                    // 다음 블록 이동
        PUT(HDRP(bp), PACK(bsize - asize, 0)); // 남은 가용 블록의 header 설정
        PUT(FTRP(bp), PACK(bsize - asize, 0)); // 남은 가용 블록의 footer 설정

        putFreeBlock(bp); // 가용리스트 첫번째에 분할된 새로운 가용블록 삽입
    } else {
        // 가용 블록을 분할할 만큼의 공간이 없는 경우
        PUT(HDRP(bp), PACK(bsize, 1)); // 가용 블록 전체를 할당된 블록으로 설정
        PUT(FTRP(bp), PACK(bsize, 1)); // 가용 블록 전체를 할당된 블록으로 설정
    }
}

/*
 * coalesce - 인접 가용블록과 병합
 */
static void *coalesce(void *bp) {
    size_t prev_alloc = GET_ALLOC(FTRP(PREV_BLKP(bp)));
    size_t next_alloc = GET_ALLOC(HDRP(NEXT_BLKP(bp)));
    size_t size = GET_SIZE(HDRP(bp));

    // case1 : 이전 블록은 할당되어 있고 다음 블록은 가용 상태인 경우
    if (prev_alloc && !next_alloc) {
        removeBlock(NEXT_BLKP(bp));              // 일단 다음 블록 삭제
        size += GET_SIZE(HDRP(NEXT_BLKP(bp)));   // 현재 블록의 크기 증가(+다음블록의 header size)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0)); // 다음 bp 기준으로 footer 가용블록 설정
        PUT(HDRP(bp), PACK(size, 0));            // 련재 bp 기준으로 header 가용블록 설정

    }
    // case2 : 이전 블록은 가용 상태이고 다음 블록은 할당되어 있는 경우
    else if (!prev_alloc && next_alloc) {
        removeBlock(PREV_BLKP(bp));            // 일단 이전 블록 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(bp))); // 현재 블록의 크기 증가(+이전블록의 header size)
        PUT(FTRP(bp), PACK(size, 0));          // 현재 bp 기준으로 footer 가용블록 설정
        bp = PREV_BLKP(bp);                    // 현재 bp를 이전 블록으로 변환
        PUT(HDRP(bp), PACK(size, 0));          // 현재 bp(이전 블록) 기준으로 header 가용블록 설정

    }
    // case3 : 이전 블록과 다음 블록이 모두 가용 상태인 경우
    else if (!prev_alloc && !next_alloc) {
        removeBlock(PREV_BLKP(bp));                                            // 일단 이전 블록 삭제
        removeBlock(NEXT_BLKP(bp));                                            // 일단 다음 블록 삭제
        size += GET_SIZE(HDRP(PREV_BLKP(bp))) + GET_SIZE(FTRP(NEXT_BLKP(bp))); // 현재 블록의 크기 증가(+이전블록의 header size,다음블록의 header size)
        PUT(FTRP(NEXT_BLKP(bp)), PACK(size, 0));                               // 다음 bp 기준으로 footer 가용블록 설정
        bp = PREV_BLKP(bp);                                                    // 현재 bp를 이전 블록으로 변환
        PUT(HDRP(bp), PACK(size, 0));                                          // 현재 bp(이전 블록) 기준으로 header 가용블록 설정
    }

    putFreeBlock(bp); // 병합 후 가용블록을 가용리스트에 삽입
    return bp;
}

/*
 * putFreeBlock -가용리스트에 가용블록 삽입(root의 앞)-stack구조
 */
void putFreeBlock(void *bp) {
    int class_idx = get_class(GET_SIZE(HDRP(bp)));
    SUCC_FREEP(bp) = GET_ROOT(class_idx);     // 현재 가용블록의 이전을 root로 설정
    PRED_FREEP(bp) = NULL;                    // 현재 가용블록의 앞을 NULL로 설정
    if (GET_ROOT(class_idx) != NULL)          // 해당 클래스에 가용블록이 하나도 없을 경우
        PRED_FREEP(GET_ROOT(class_idx)) = bp; // 클래스의 첫번째 가용블록을 현재 가용블록으로 설정
    GET_ROOT(class_idx) = bp;                 // 해당 클래스의 root를 현재 가용블록으로 변경
}

/*
 * removeBlock - 가용리스트에서 블록 제거
 */
void removeBlock(void *bp) {
    int class_idx = get_class(GET_SIZE(HDRP(bp)));
    if (bp == GET_ROOT(class_idx)) {          // 삭제할 블록이 해당 클래스의 root일 경우
        GET_ROOT(class_idx) = SUCC_FREEP(bp); // 삭제할 블록의 이전을 root로 설정
    } else {
        SUCC_FREEP(PRED_FREEP(bp)) = SUCC_FREEP(bp); // 삭제할 블록의 앞블록과 이전블록을 연결
        if (SUCC_FREEP(bp) != NULL)
            PRED_FREEP(SUCC_FREEP(bp)) = PRED_FREEP(bp); // 삭제할 블록의 앞블록과 이전블록을 연결
    }
}

/*
 * get_class - 요청된 size가 segregated_list중 해당하는 class 찾기
 */
int get_class(size_t size) {
    int class_idx = 16;
    for (int i = 0; i < LISTLIMIT; i++) {
        if (size <= class_idx)
            return i;
        class_idx <<= 1;
    }
    return LISTLIMIT - 1;
}
