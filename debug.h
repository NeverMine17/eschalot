/* Spam STDERR with diagnostic messages... */
void verbose(char *message, ...)
{
    va_list	ap;

    va_start(ap, message);
    vfprintf(stderr, message, ap);
    va_end(ap);
    fflush(stderr);
}

/* ...or be a very quiet thinker. */
void
normal(__attribute__((unused)) char *unused, ...)
{

}

/* Print error message and exit. */
/* (Not all Linuxes implement the err/errx functions properly.) */
void error(char *message, ...)
{
    va_list	ap;

    va_start(ap, message);
    std::cout << "ERROR: ";
    std::cout << message << ap << std::endl;
    va_end(ap);
    exit(1);
}