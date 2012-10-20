module SEQ
{
  protecting( NAT )
  [Nat < Seq]
  signature {
    op empty-seq :
      ->	Seq
    op _ ^ _ :
      Nat
	Seq
	  ->	Seq
	    { r-assoc } 	    -- { r-assoc id: empty-seq }

  }
}

module SEQSEQ1
{
  protecting( SEQ )
  [Seq < SeqSeq]
  signature {
    op empty-seq-seq :
      ->	SeqSeq
    op _ & _ :
      Seq
	SeqSeq
	  ->	SeqSeq 
	    { r-assoc }
	    -- { id: empty-seq-seq }
    op tail :
      SeqSeq
	->	SeqSeq
  }
  axioms {
    var	SEQ : Seq
    var	SEQSEQ : SeqSeq
    eq	tail(
	       SEQ	&	SEQSEQ
		 )
    =	SEQSEQ .
    eq	tail(
	       empty-seq-seq
		 )
    =	empty-seq-seq .
  }
}


module SEQSEQ2
{
  protecting( SEQ )
  [Seq < SeqSeq]
  signature {
    op empty-seq-seq :
      ->	SeqSeq
    op _ & _ :
      SeqSeq
	SeqSeq
	  ->	SeqSeq
	    { assoc id: empty-seq-seq }
    op tail :
      SeqSeq
	->	SeqSeq
  }
  axioms {
    var	SEQ : Seq
    var	SEQSEQ : SeqSeq
    eq	tail(
	       SEQ	&	SEQSEQ
		 )
    =	SEQSEQ .
    eq	tail(
	       empty-seq-seq
		 )
    =	empty-seq-seq .
  }
}
