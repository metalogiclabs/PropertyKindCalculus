package HarmonicOscillatorPKC {
    doc /* A hand-authored PKC model exercising the three layers of the DSL. */
    private import PKC::*;
    private import PKC::Kinds::*;
    private import PKC::Modules::*;
    private import PKC::Tape::*;

    #principle transverseExtent { :>> id = "transverse-extent"; }

    #kind length {
        :>> id default = "length"; :>> scale default = ScaleType::ratio;
        attribute dimL :> dimension { :>> base default = "length"; :>> num default = 1; }
        :>> standardRef default = "ISO 80000-3:2019"; :>> catalogueItem default = "3-1.1"; :>> symbol default = "l"; :>> coherentUnit default = "m";
        @Source { decl = "PropertyKindCalculus.Iso80000.Part3.length"; }
    }
    #kind width :> length {
        :>> id default = "width"; :>> principle default = transverseExtent; :>> catalogueItem default = "3-1.2"; :>> symbol default = "b";
        @Checked { decl = "PropertyKindCalculus.Iso80000.Part3.Edge.width_length"; }
    }
    #kind angularFrequency { :>> id default = "angular frequency"; :>> scale default = ScaleType::ratio; }
    #kind angularFrequencySquared { :>> id default = "angular frequency squared"; :>> scale default = ScaleType::ratio; }
    #kind mass { :>> id default = "mass"; :>> scale default = ScaleType::ratio; }
    #kind stiffness { :>> id default = "mass × angular frequency²"; :>> scale default = ScaleType::ratio; }

    #product connection omegaSquared : KindProduct
        connect (left ::> angularFrequency, right ::> angularFrequency, result ::> angularFrequencySquared) {
        :>> table = true;
    }
    #quotient connection omegaFromStiffness : KindQuotient
        connect (numerator ::> stiffness, denominator ::> mass, result ::> angularFrequencySquared);

    #unit metre { :>> kind = length; :>> symbol = "m"; }

    #module oscillator : Module {
        :>> name = "oscillator";
        port m : KindPort { :>> node = "m"; :>> kind = mass; :>> dir = PortDir::input; }
        port k : KindPort { :>> node = "k"; :>> kind = stiffness; :>> dir = PortDir::param; }
        port omega2 : KindPort { :>> node = "result"; :>> kind = angularFrequencySquared; :>> dir = PortDir::output; }
        attribute occ0 :> occurrences {
            :>> family = EdgeFamily::quotient;
            attribute opK :> operands { :>> node = "k"; :>> kind = stiffness; }
            attribute opM :> operands { :>> node = "m"; :>> kind = mass; }
            :>> result = "result"; :>> resultKind = angularFrequencySquared;
            :>> site = "Attempt4Pkc.omegaSq";
        }
        :>> exits = "result";
    }
    #module oscillatorSpec : Module { :>> name = "oscillatorSpec"; :>> role = BoundaryRole::specification; }

    #relation connection oscillatorEquals : Relation connect (left ::> oscillator, right ::> oscillatorSpec) {
        :>> kind = RelationKind::equals;
        :>> witness = "Attempt4Pkc.omegaSq_equals_spec";
        attribute floatLicense :> licenses { :>> rung = "Float"; :>> transfer = TransferKind::exact; :>> witness = "Attempt4Pkc.omegaSq_float"; }
    }

    #req requirement positiveStiffness : PkcRequirement {
        :>> name = "positiveStiffness";
        :>> statement = "stiffness is strictly positive";
        :>> kind = RequirementKind::provable;
        :>> governs = "oscillator";
        :>> witness = "Attempt4Pkc.stiffness_pos";
    }

    #tape oscillatorTape : TapeGraph {
        attribute v0 :> vertices { :>> name = "k"; }
        attribute v1 :> vertices { :>> name = "m"; }
        attribute v2 :> vertices { :>> name = "div"; :>> parents = (0, 1); }
    }
    #match connection oscillatorMatch : Match connect (module ::> oscillator, tape ::> oscillatorTape) {
        attribute cK :> components { :>> node = "k"; :>> vertices = 0; }
        attribute cM :> components { :>> node = "m"; :>> vertices = 1; }
        attribute cR :> components { :>> node = "result"; :>> vertices = 2; }
        attribute r0 :> realized { :>> occ = 0; }
        attribute :>> carrier { :>> rung = "tape"; :>> platform = "cuda"; }
    }
}
