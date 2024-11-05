
fun generic[T](){
    fun thingy(){
        print(typename(T));
    }
    thingy();
}


fun make_generic[T]()->fun(fun()->T)->T{
    return fun(maker:fun()->T)->T{
        maker()
    }
}
print(make_generic:[int]()(fun()->int { 5}));
print(make_generic:[float]()(fun()->float { 0.1}));
print(make_generic:[string]()(fun()->string { "Yo long time no see."}));
