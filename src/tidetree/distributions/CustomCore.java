package tidetree.distributions;

import beast.base.core.Description;
import beast.base.evolution.likelihood.BeerLikelihoodCore;
import beast.base.evolution.sitemodel.SiteModelInterface;
import beast.base.evolution.tree.Node;
import tidetree.substitutionmodel.EditAndSilencingModel;

/**
 * @author Sophie Seidel
 **/
@Description("Contains methods to calculate the partial likelihoods.")
public class CustomCore extends BeerLikelihoodCore {


    private double editStart;
    private double editStop;
    
    public CustomCore(int nrOfStates) {
        super(nrOfStates);
    }

    /**
     * initializes partial likelihood arrays.
     *  @param nodeCount           the number of nodes in the tree
     * @param patternCount        the number of patterns
     * @param matrixCount         the number of matrices (i.e., number of categories)
     * @param integrateCategories whether sites are being integrated over all matrices
     * @param m_siteModel
     */

    public void initialize(int nodeCount, int patternCount, int matrixCount, boolean integrateCategories, boolean useAmbiguities,
                           EditAndSilencingModel substitutionModel, SiteModelInterface.Base m_siteModel) {

        super.initialize(nodeCount, patternCount, matrixCount, integrateCategories, useAmbiguities);
        
        
        this.editStart = substitutionModel.getEditHeight();
        this.editStop = editStart - substitutionModel.getEditDuration();
    }

    /**
     * Calculates partial likelihoods at a node.
     *
     * @param child1 the 'child 1' node
     * @param child2 the 'child 2' node
     * @param node the 'parent' node
     */
    public void calculatePartials(Node child1, Node child2, Node node, double dropoutProb) {

        int nodeIndex1 = child1.getNr();
        int nodeIndex2 = child2.getNr();
        int nodeIndex3 = node.getNr();

            if (states[nodeIndex1] != null) {
                if (states[nodeIndex2] != null) {
                    calculateStatesStatesPruning(
                            states[nodeIndex1], matrices[currentMatrixIndex[nodeIndex1]][nodeIndex1],
                            states[nodeIndex2], matrices[currentMatrixIndex[nodeIndex2]][nodeIndex2],
                            partials[currentPartialsIndex[nodeIndex3]][nodeIndex3], dropoutProb);
                } else {
                    calculateStatesPartialsPruning(states[nodeIndex1], matrices[currentMatrixIndex[nodeIndex1]][nodeIndex1],
                            partials[currentPartialsIndex[nodeIndex2]][nodeIndex2], matrices[currentMatrixIndex[nodeIndex2]][nodeIndex2],
                            partials[currentPartialsIndex[nodeIndex3]][nodeIndex3], dropoutProb);
                }
            } else {
                if (states[nodeIndex2] != null) {
                    calculateStatesPartialsPruning(states[nodeIndex2], matrices[currentMatrixIndex[nodeIndex2]][nodeIndex2],
                            partials[currentPartialsIndex[nodeIndex1]][nodeIndex1], matrices[currentMatrixIndex[nodeIndex1]][nodeIndex1],
                            partials[currentPartialsIndex[nodeIndex3]][nodeIndex3], dropoutProb );
                } else {
                    calculatePartialsPartialsPruning(partials[currentPartialsIndex[nodeIndex1]][nodeIndex1], matrices[currentMatrixIndex[nodeIndex1]][nodeIndex1],
                            partials[currentPartialsIndex[nodeIndex2]][nodeIndex2], matrices[currentMatrixIndex[nodeIndex2]][nodeIndex2],
                            partials[currentPartialsIndex[nodeIndex3]][nodeIndex3]);
                }
            }

        if (useScaling) {
            scalePartials(nodeIndex3);
        }

//
//        int k =0;
//        for (int i = 0; i < patternCount; i++) {
//            double f = 0.0;
//
//            for (int j = 0; j < stateCount; j++) {
//                f += partials[currentPartialsIndices[nodeIndex3]][nodeIndex3][k];
//                k++;
//            }
//            if (f == 0.0) {
//                Logger.getLogger("error").severe("A partial likelihood (node index = " + nodeIndex3 + ", pattern = "+ i +") is zero for all states.");
//            }
//        }
    }

    public void calculatePartials(Node child1, Node node, double dropoutProb) {

        int nodeIndex1 = child1.getNr();
        int nodeIndex3 = node.getNr();

        if (states[nodeIndex1] != null) {
            calculateStatesPruning(states[nodeIndex1],matrices[currentMatrixIndex[nodeIndex1]][nodeIndex1],partials[currentPartialsIndex[nodeIndex3]][nodeIndex3],dropoutProb);
        } else {
            calculatePartialsPruning(partials[currentPartialsIndex[nodeIndex1]][nodeIndex1],
            matrices[currentMatrixIndex[nodeIndex1]][nodeIndex1], partials[currentPartialsIndex[nodeIndex3]][nodeIndex3],dropoutProb);
        }

        if (useScaling) {
            scalePartials(nodeIndex3);
        }
    }


    void calculatePartialsForCrossBranches(Node parent, Node child1, Node child2, boolean bool1, boolean bool2,
                                           SiteModelInterface.Base m_siteModel, EditAndSilencingModel substitutionModel,
                                           double branchRate){

        double[] nodePartials = new double[partialsSize];
        double[][] helperNodePartials = new double[4][partialsSize];

        double[] jointBranchRates0 = new double[nrOfMatrices];
        double[] jointBranchRates1 = new double [nrOfMatrices];

        for (int i = 0; i < nrOfMatrices; i++){
            jointBranchRates0[i] = m_siteModel.getRateForCategory(i, child1) * branchRate;
            jointBranchRates1[i] = m_siteModel.getRateForCategory(i, child2) * branchRate;
        }

        Node[] children = new Node[]{child1, child2};
        int[] childIndices = new int[]{child1.getNr(), child2.getNr()};
        double[][] jointbranchRates = new double[][]{jointBranchRates0, jointBranchRates1};

        double[] heightsBeforeParent = new double[2];
        boolean[] needsIntermediates = new boolean[2];

        double[] probs0 = new double[(nrOfStates) * (nrOfStates)];
        double[] probs1 = new double[(nrOfStates) * (nrOfStates)];
        double [] matrix0 = new double[nrOfMatrices * matrixSize];
        double [] matrix1 = new double[nrOfMatrices * matrixSize];

        // determine the number of helper nodes to calculate the partials over
        int nIntermediateNodes;
        double[] intNodeTimes;

        boolean [] parentBeforeChildAfterEditStart = new boolean[] {
                (parent.getHeight() > editStart) & (child1.getHeight() < editStart),
                (parent.getHeight() > editStart) & (child2.getHeight() < editStart)
        };
        boolean [] parentBeforeChildAfterEditStop = new boolean[]{
                (parent.getHeight() > editStop) & (child1.getHeight() < editStop),
                (parent.getHeight() > editStop) & (child2.getHeight() < editStop)
        };

        // for each child calculate partials upwards until the helper node below the parent
        // that's only necessary if the rate matrix changes on the branch!
        for (int i=0; i< children.length; i++){

            // if parent above edit window (sw), child in sw
            if (parentBeforeChildAfterEditStart[i] & !parentBeforeChildAfterEditStop[i]){
                nIntermediateNodes = 1;
                intNodeTimes = new double[]{children[i].getHeight(), editStart, Double.NEGATIVE_INFINITY};
                heightsBeforeParent[i] = editStart;
                needsIntermediates[i] = true;

                helperNodePartials[i * 2 + 1] = calculatePartialsBeforeParent(parent, children[i], i, childIndices[i],
                        intNodeTimes, jointbranchRates[i], nIntermediateNodes, helperNodePartials, substitutionModel);

                // if parent in sw and child below sw
            }else if(!parentBeforeChildAfterEditStart[i] & parentBeforeChildAfterEditStop[i]){
                nIntermediateNodes = 1;
                intNodeTimes = new double[]{children[i].getHeight(), editStop, Double.NEGATIVE_INFINITY};
                heightsBeforeParent[i] = editStop;
                needsIntermediates[i] = true;

                helperNodePartials[i * 2 + 1] = calculatePartialsBeforeParent(parent, children[i], i, childIndices[i],
                        intNodeTimes, jointbranchRates[i], nIntermediateNodes, helperNodePartials, substitutionModel);

                // if parent above sw and child below sw
            }else if (parentBeforeChildAfterEditStart[i] & parentBeforeChildAfterEditStop[i]){
                nIntermediateNodes = 2;
                intNodeTimes = new double[]{children[i].getHeight(), editStop, editStart};
                heightsBeforeParent[i] = editStart;
                needsIntermediates[i] = true;

                helperNodePartials[i * 2 + 1] = calculatePartialsBeforeParent(parent, children[i], i, childIndices[i],
                        intNodeTimes, jointbranchRates[i], nIntermediateNodes, helperNodePartials, substitutionModel);

                // parent and child in the same rate matrix regime
            }else{
                heightsBeforeParent[i] = children[i].getHeight();
                needsIntermediates[i] = false;
            }
        }


        //calculate partials at parent
        // if intermediates are necessary their *partials* were computed above -> no leaf check necessary
        if (needsIntermediates[0]) {
            for (int k = 0; k < nrOfMatrices; k++) {
                substitutionModel.getTransitionProbabilities(null, parent.getHeight(), heightsBeforeParent[0],
                        jointBranchRates0[k], probs0);
                System.arraycopy(probs0, 0, matrix0, k * matrixSize, matrixSize);
            }

            if (needsIntermediates[1]) {
                for (int k = 0; k < nrOfMatrices; k++) {
                    substitutionModel.getTransitionProbabilities(null, parent.getHeight(), heightsBeforeParent[1],
                            jointBranchRates1[k], probs1);
                    System.arraycopy(probs1, 0, matrix1, k * matrixSize, matrixSize);
                }
                calculatePartialsPartialsPruning(helperNodePartials[1], matrix0, helperNodePartials[3], matrix1, nodePartials);

            } else {
                for (int k = 0; k < nrOfMatrices; k++) {
                    substitutionModel.getTransitionProbabilities(null, parent.getHeight(), child2.getHeight(),
                            jointBranchRates1[k], probs1);
                    System.arraycopy(probs1, 0, matrix1, k * matrixSize, matrixSize);
                }

                if (child2.isLeaf()) {
                    int[] states = new int[nrOfPatterns];
                    getNodeStates(childIndices[1], states);

                    calculateStatesPartialsPruning(states, matrix1, helperNodePartials[1], matrix0, nodePartials);

                } else {
                    double[] partials = new double[partialsSize];
                    getNodePartials(childIndices[1], partials);
                    calculatePartialsPartialsPruning(partials, matrix1, helperNodePartials[1], matrix0, nodePartials);
                }
            }
        } else {
            for (int k = 0; k < nrOfMatrices; k++) {
                substitutionModel.getTransitionProbabilities(null, parent.getHeight(), child1.getHeight(),
                        jointBranchRates0[k], probs0);
                System.arraycopy(probs0, 0, matrix0, k * matrixSize, matrixSize);
            }

            if (child1.isLeaf()){
                int[] states1 = new int[nrOfPatterns];
                getNodeStates(childIndices[0], states1);

                if (needsIntermediates[1]){
                    for (int k = 0; k < nrOfMatrices; k++) {
                        substitutionModel.getTransitionProbabilities(null, parent.getHeight(), heightsBeforeParent[1],
                                jointBranchRates1[k], probs1);
                        System.arraycopy(probs1, 0, matrix1, k * matrixSize, matrixSize);
                    }

                    // because helper node partials were computed, we can directly take them as input
                    calculateStatesPartialsPruning(states1, probs0, helperNodePartials[3], probs1, nodePartials);
                }else{
                    // because no helper nodes were needed, we have to check child2 being a leaf or not
                    for (int k = 0; k < nrOfMatrices; k++) {
                        substitutionModel.getTransitionProbabilities(null, parent.getHeight(), child2.getHeight(),
                                jointBranchRates1[k], probs1);
                        System.arraycopy(probs1, 0, matrix1, k * matrixSize, matrixSize);
                    }

                    if (child2.isLeaf()){
                        int[] states2 = new int [nrOfPatterns];
                        getNodeStates(childIndices[1], states2);
                        calculateStatesStatesPruning(states1, matrix0, states2, matrix1, nodePartials);
                    }else{
                        double[] partials2 = new double[partialsSize];
                        getNodePartials(childIndices[1], partials2);
                        calculateStatesPartialsPruning(states1, matrix0, partials2, matrix1, nodePartials);
                    }
                }
            }else {
                double[] partials1 = new double[partialsSize];
                getNodePartials(childIndices[0], partials1);

                if (needsIntermediates[1]){
                    for (int k = 0; k < nrOfMatrices; k++) {
                        substitutionModel.getTransitionProbabilities(null, parent.getHeight(), heightsBeforeParent[1],
                                jointBranchRates1[k], probs1);
                        System.arraycopy(probs1, 0, matrix1, k * matrixSize, matrixSize);
                    }
                    calculatePartialsPartialsPruning(partials1, matrix0, helperNodePartials[3], matrix1, nodePartials);
                }else{
                    for (int k = 0; k < nrOfMatrices; k++) {
                        substitutionModel.getTransitionProbabilities(null, parent.getHeight(), child2.getHeight(),
                                jointBranchRates1[k], probs1);
                        System.arraycopy(probs1, 0, matrix1, k * matrixSize, matrixSize);
                    }

                    if (child2.isLeaf()){
                        int[] states2 = new int [nrOfPatterns];
                        getNodeStates(childIndices[1], states2);
                        calculateStatesPartialsPruning(states2, matrix1, partials1, matrix0, nodePartials);
                    }else{
                        double[] partials2 = new double[partialsSize];
                        getNodePartials(childIndices[1], partials2);
                        calculatePartialsPartialsPruning(partials2, matrix1, partials1, matrix0, nodePartials);
                    }
                }
            }
        }
        setCurrentNodePartials(parent.getNr(), nodePartials);
        if (useScaling) {
            scalePartials(parent.getNr());
        }
    }

    void calculatePartialsForCrossBranches(Node parent, Node child, boolean bool1, boolean bool2,
                                           SiteModelInterface.Base m_siteModel, EditAndSilencingModel substitutionModel,
                                           double branchRate){

        double[] nodePartials = new double[partialsSize];
        double[][] helperNodePartials = new double[4][partialsSize];

        double[] jointBranchRates = new double[nrOfMatrices];


        for (int i = 0; i < nrOfMatrices; i++){
            jointBranchRates[i] = m_siteModel.getRateForCategory(i, child) * branchRate;
        }

        int childIndx = child.getNr();

        double heightsBeforeParent = -1.0;
        boolean needsIntermediates = false;

        double[] probs = new double[(nrOfStates) * (nrOfStates)];
        double [] matrix = new double[nrOfMatrices * matrixSize];

        // determine the number of helper nodes to calculate the partials over
        int nIntermediateNodes;
        double[] intNodeTimes;

        boolean  parentBeforeChildAfterEditStart =
                (parent.getHeight() > editStart) & (child.getHeight() < editStart);
        boolean parentBeforeChildAfterEditStop =
                (parent.getHeight() > editStop) & (child.getHeight() < editStop);

        // calculate partials upwards until the helper node below the parent
        // that's only necessary if the rate matrix changes on the branch!


        // if parent above edit window (sw), child in sw
        if (parentBeforeChildAfterEditStart & !parentBeforeChildAfterEditStop){
                nIntermediateNodes = 1;
                intNodeTimes = new double[]{child.getHeight(), editStart, Double.NEGATIVE_INFINITY};
                heightsBeforeParent = editStart;
                needsIntermediates = true;

                helperNodePartials[1] = calculatePartialsBeforeParent(parent, child, 0, childIndx,
                        intNodeTimes, jointBranchRates, nIntermediateNodes, helperNodePartials, substitutionModel);

                // if parent in sw and child below sw
        }else if(!parentBeforeChildAfterEditStart & parentBeforeChildAfterEditStop){
                nIntermediateNodes = 1;
                intNodeTimes = new double[]{child.getHeight(), editStop, Double.NEGATIVE_INFINITY};
                heightsBeforeParent = editStop;
                needsIntermediates = true;

                helperNodePartials[1] = calculatePartialsBeforeParent(parent, child, 0, childIndx,
                        intNodeTimes, jointBranchRates, nIntermediateNodes, helperNodePartials, substitutionModel);

                // if parent above sw and child below sw
        }else if (parentBeforeChildAfterEditStart & parentBeforeChildAfterEditStop){
                nIntermediateNodes = 2;
                intNodeTimes = new double[]{child.getHeight(), editStop, editStart};
                heightsBeforeParent = editStart;
                needsIntermediates = true;

                helperNodePartials[1] = calculatePartialsBeforeParent(parent, child, 0, childIndx,
                        intNodeTimes, jointBranchRates, nIntermediateNodes, helperNodePartials, substitutionModel);

                // parent and child in the same rate matrix regime
        }else{
                heightsBeforeParent = child.getHeight();
                needsIntermediates = false;
        }



        //calculate partials at parent
        // if intermediates are necessary their *partials* were computed above -> no leaf check necessary
        if (needsIntermediates) {
            for (int k = 0; k < nrOfMatrices; k++) {
                substitutionModel.getTransitionProbabilities(null, parent.getHeight(), heightsBeforeParent,
                        jointBranchRates[k], probs);
                System.arraycopy(probs, 0, matrix, k * matrixSize, matrixSize);
            }
            calculatePartialsPruning(helperNodePartials[1], matrix, nodePartials, substitutionModel.getDropoutProbability());

        } else {
            for (int k = 0; k < nrOfMatrices; k++) {
                substitutionModel.getTransitionProbabilities(null, parent.getHeight(), child.getHeight(),
                        jointBranchRates[k], probs);
                System.arraycopy(probs, 0, matrix, k * matrixSize, matrixSize);
            }

            if (child.isLeaf()){
                int[] states = new int[nrOfPatterns];
                getNodeStates(childIndx, states);

                calculateStatesPruning(states, matrix, nodePartials, substitutionModel.getDropoutProbability());

            }else {
                double[] partials = new double[partialsSize];
                getNodePartials(childIndx, partials);

                calculatePartialsPruning(partials, matrix, nodePartials,substitutionModel.getDropoutProbability());
            }
        }
        setCurrentNodePartials(parent.getNr(), nodePartials);
        if (useScaling) {
            scalePartials(parent.getNr());
        }
    }

    double[] calculatePartialsBeforeParent(Node parent, Node child, int i, int childIndex, double[] intNodeTimes, double[] jointBranchRates, int nIntermediateNodes, double[][] helperNodePartials,
                                           EditAndSilencingModel substitutionModel) {

        double [] matrix = new double[nrOfMatrices * matrixSize];
        double[] probs = new double[matrixSize];

        if (child.isLeaf()) {
            int[] states = new int[nrOfPatterns];
           getNodeStates(childIndex, states);

            if (nIntermediateNodes == 0) {
                for (int k = 0; k < nrOfMatrices; k++){
                    substitutionModel.getTransitionProbabilities(null, parent.getHeight(), child.getHeight(), jointBranchRates[k], probs);
                    System.arraycopy(probs, 0, matrix, k * matrixSize, matrixSize);
                }
                helperNodePartials[i * 2 + 1] = calculateStatesPruning(states, matrix, helperNodePartials[i * 2 + 1], substitutionModel.getDropoutProbability());



            } else {
                for (int k = 0; k < nrOfMatrices; k++) {
                    substitutionModel.getTransitionProbabilities(null, intNodeTimes[1], intNodeTimes[0], jointBranchRates[k], probs);
                    System.arraycopy(probs, 0, matrix, k * matrixSize, matrixSize);
                }
                helperNodePartials[i * 2] = calculateStatesPruning(states, matrix, helperNodePartials[i * 2], substitutionModel.getDropoutProbability());
                helperNodePartials[i * 2 + 1] = helperNodePartials[i * 2];


                if (nIntermediateNodes > 1) {
                    for (int k = 0; k < nrOfMatrices; k++) {
                        substitutionModel.getTransitionProbabilities(null, intNodeTimes[2], intNodeTimes[1], jointBranchRates[k], probs);
                        System.arraycopy(probs, 0, matrix, k * matrixSize, matrixSize);
                    }
                    helperNodePartials[i * 2 + 1] = calculatePartialsPruning(helperNodePartials[i * 2], matrix, helperNodePartials[i * 2 + 1], substitutionModel.getDropoutProbability());

                }
            }
        } else {
            double[] partials = new double[partialsSize];
            getNodePartials(childIndex, partials);

            if (nIntermediateNodes == 0) {
                for (int k = 0; k < nrOfMatrices; k++) {
                    substitutionModel.getTransitionProbabilities(null, parent.getHeight(), child.getHeight(), jointBranchRates[k], probs);
                    System.arraycopy(probs, 0, matrix, k * matrixSize, matrixSize);
                }
                    helperNodePartials[i * 2 + 1] = calculatePartialsPruning(partials, matrix, helperNodePartials[i * 2 + 1], substitutionModel.getDropoutProbability());
            } else {

                helperNodePartials[i * 2] = partials;
                for (int j = 0; j < nIntermediateNodes; j++) {
                    for (int k = 0; k < nrOfMatrices; k++) {
                        substitutionModel.getTransitionProbabilities(null, intNodeTimes[j + 1], intNodeTimes[j], jointBranchRates[k], probs);
                        System.arraycopy(probs, 0, matrix, k * matrixSize, matrixSize);
                    }
                    helperNodePartials[i * 2 + 1] = calculatePartialsPruning(helperNodePartials[i * 2], matrix, helperNodePartials[i * 2 + 1], substitutionModel.getDropoutProbability());
                    helperNodePartials[i * 2] = helperNodePartials[i * 2 + 1];

                }
            }
        }

        return helperNodePartials[i * 2 + 1];
    }


    protected double[] calculateStatesPruning(int[] stateIndex1, double[] matrices1,
                                              double[] partials3, double dropoutProb) {
        int v = 0;
        double sum1;

        for (int l = 0; l < nrOfMatrices; l++) {

            for (int k = 0; k < nrOfPatterns; k++) {

                int state1 = stateIndex1[k];

                int w = l * matrixSize;

                //state is scarred
                if (state1 < nrOfStates - 1) {


                    for (int i = 0; i < nrOfStates; i++) {
                        //state evolved to the observed state and didn't go missing
                        partials3[v] = matrices1[w + state1] * (1 - dropoutProb);

                        v++;
                        w += nrOfStates;
                    }

                    //state is silenced/lost
                } else {


                    for (int i = 0; i < nrOfStates; i++) {
                        //state got silenced, and then went missing, or state evolved and went missing
                        partials3[v] = matrices1[w + nrOfStates - 1] +  (1 - matrices1[w + nrOfStates - 1]) * (dropoutProb);

                        v++;
                        w += nrOfStates;
                    }


                }
            }
        }
        return partials3;
    }

    // calculate partials for single child nodes
    protected double[] calculatePartialsPruning(double[] partials1, double[] matrices1,
                                                double[] partials3, double dropoutProb) {
        double sum1;

        int u = 0;
        int v = 0;

        for (int l = 0; l < nrOfMatrices; l++) {

            for (int k = 0; k < nrOfPatterns; k++) {

                int w = l * matrixSize;

                for (int i = 0; i < nrOfStates; i++) {

                    sum1 = 0.0;

                    for (int j = 0; j < nrOfStates; j++) {
                        sum1 += matrices1[w] * partials1[v + j];

                        w++;
                    }

                    partials3[u] = sum1;
                    u++;
                }
                v += nrOfStates;
            }
        }
        return partials3;
    }

    /**
     * Calculates partial likelihoods at a node when both children have states.
     */
    protected void calculateStatesStatesPruning(int[] stateIndex1, double[] matrices1,
                                                int[] stateIndex2, double[] matrices2,
                                                double[] partials3, double dropoutProb) {
        int v = 0;


        for (int l = 0; l < nrOfMatrices; l++) {

            for (int k = 0; k < nrOfPatterns; k++) {

                int state1 = stateIndex1[k];
                int state2 = stateIndex2[k];

                int w = l * matrixSize;

                if (state1 < nrOfStates - 1  && state2 < nrOfStates - 1) {

                    for (int i = 0; i < nrOfStates; i++) {
                        //both states evolved to the observed states and didn't go missing
                        partials3[v] = matrices1[w + state1] *  (1 - dropoutProb) * matrices2[w + state2] * (1 - dropoutProb);

                        v++;
                        w += nrOfStates;
                    }

                } else if (state2 < nrOfStates - 1) {

                    //from unedited to any state + dropout or from unedited to silenced + dropout

                    for (int i = 0; i < nrOfStates; i++) {
                        //one statee evolved to the observed state and didn't go missing
                        //state got silenced, and then went missing, or state evolved and went missing
                        partials3[v] = (matrices1[w + nrOfStates - 1] +  (1 - matrices1[w + nrOfStates - 1]) * (dropoutProb)) *  matrices2[w + state2] * (1 - dropoutProb);

                        v++;
                        w += nrOfStates;
                    }


                } else if (state1 < nrOfStates - 1) {

                    for (int i = 0; i < nrOfStates; i++) {
                        //one statee evolved to the observed state and didn't go missing
                        //state got silenced, and then went missing, or state evolved and went missing
                        partials3[v] = (matrices2[w + nrOfStates - 1] +  (1 - matrices2[w + nrOfStates - 1]) * (dropoutProb)) *  matrices1[w + state1] * (1 - dropoutProb);

                        v++;
                        w += nrOfStates;
                    }

                } else {

                    for (int i = 0; i < nrOfStates; i++) {
                        //both states eithr got silenced, and then went missing, or state evolved and went missing
                        partials3[v] = (matrices2[w + nrOfStates - 1] +  (1 - matrices2[w + nrOfStates - 1]) * (dropoutProb)) * (matrices1[w + nrOfStates - 1] +  (1 - matrices1[w + nrOfStates - 1]) * (dropoutProb));

                        v++;
                        w += nrOfStates;
                    }


                }
            }
        }
    }

    /**
     * Calculates partial likelihoods at a node when one child has states and one has partials.
     */
    protected void calculateStatesPartialsPruning(int[] stateIndex1, double[] matrices1,
                                                  double[] partials2, double[] matrices2,
                                                  double[] partials3, double dropoutProb) {

        double sum1, sum2;

        int u = 0;
        int v = 0;

        for (int l = 0; l < nrOfMatrices; l++) {

            for (int k = 0; k < nrOfPatterns; k++) {

                int state1 = stateIndex1[k];
                int w = l * matrixSize;

                if(state1 < nrOfStates - 1) {

                    for (int i = 0; i < nrOfStates; i++) {

                        sum1 = matrices1[w + state1] *  (1 - dropoutProb);
                        sum2 = 0.0;

                        for (int j = 0; j < nrOfStates; j++) {

                            sum2 += matrices2[w] * partials2[v + j];

                            w++;
                        }

                        partials3[u] = sum1 * sum2;
                        u++;
                    }
                    v += nrOfStates;

                }
                else {

                    for (int i = 0; i < nrOfStates; i++) {

                        sum1 = (matrices1[w + nrOfStates - 1] +  (1 - matrices1[w + nrOfStates - 1]) * (dropoutProb));
                        sum2 = 0.0;

                        for (int j = 0; j < nrOfStates; j++) {

                            sum2 += matrices2[w] * partials2[v + j];

                            w++;
                        }

                        partials3[u] = sum1 * sum2;
                        u++;
                    }
                    v += nrOfStates;

                }


            }
        }

    }
}
