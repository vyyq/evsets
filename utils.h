#ifndef utils_H
#define utils_H

#include <stdlib.h>

#define SUCCESS_SYMBOL "😀"
#define QUESTION_SYMBOL "❔"
#define FAILURE_SYMBOL "❌"
#define FATAL_SYMBOL "💀"
#define SUCCESS_STATUS_PREFIX "[" SUCCESS_SYMBOL "] "
#define QUESTION_STATUS_PREFIX "[" QUESTION_SYMBOL "] "
#define FAILURE_STATUS_PREFIX "[" FAILURE_SYMBOL "] "
#define FATAL_STATUS_PREFIX "[" FATAL_SYMBOL "] "

void shuffle(int *array, size_t n);

#endif /* utils_H */
