#ifndef _DEFAULTS_H_
#define _DEFAULTS_H_

// the following packing threshold seems to be optimal
// as soon as the prop sequence outgrows this length,
// it needs to be truncated by learning a new prop clause
// otherwise the total number of propagations performed grows quadratically
#define PROP_PACKING_THRESHOLD 5
#define GRAT_BUFFER_SIZE 10000000 // bytes

#endif
