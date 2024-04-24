#include <stdint.h>
#include <stdio.h>
#include <assert.h>

void divide(uint16_t dividend, uint8_t divisor, uint16_t *quotient, uint16_t *remainder) {
    if (divisor == 0) {
        printf("Error: Division by zero.\n");
        *quotient = 0;  
        *remainder = 0; 
        return;
    }

    // Perform division and modulus
    *quotient = dividend / divisor;
    *remainder = dividend % divisor;
}

int unknown(){
    return 0;
}

int main() {
    uint16_t dividend = unknown();  
    uint8_t divisor = unknown();   
    uint16_t quotient = 0;
    uint16_t remainder = 0;

    divide(dividend, divisor, &quotient, &remainder);
    printf("Quotient: %u\n", quotient);
    printf("Remainder: %u\n", remainder);

    assert(quotient == 1 || remainder == 1);
    return 0;
}